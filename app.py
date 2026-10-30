"""
SASTRA SoME End Semester Examination Duty Portal
=================================================
Files required in the same folder as app.py:
  1. Faculty_Master.xlsx  — columns: S.No. | ID No. | NAME OF STAFF | Designation
                            (+ optional valuation date cols V1..V5)
  2. Offline_Duty.xlsx    — offline exam slots  (col A: Date | col B: FN/AN | col C: count)
  3. sastra_logo.png      — university logo (optional)
  4. faculty_passwords.json — auto-created on first run; keyed by Faculty ID No.

Login:
  Faculty portal : enter your Faculty ID (e.g. C870, RS602) + password
  Default password on first login: "sastra" (forced change on first use)
  Admin panel    : any faculty marked is_admin=true in faculty_passwords.json

v5 — ID-based login | bcrypt passwords | resubmission | accommodation stats
     Core optimizer: scipy HiGHS MILP | Smart Greedy | OR-Tools CP-SAT
     NOTE: Online duty suspended this semester — all duties are Offline only.
     Semester: Odd Semester 2026-27 (Nov/Dec 2026) — see SEMESTER CONFIG block.
"""

import os
import re
import io
import json
import secrets
import datetime
import warnings
import logging
import calendar as calmod
import urllib.parse
from collections import defaultdict

import numpy as np
import pandas as pd
import streamlit as st
import altair as alt
from supabase import create_client, Client

logging.getLogger("streamlit").setLevel(logging.ERROR)

try:
    import bcrypt
    BCRYPT_OK = True
except ImportError:
    BCRYPT_OK = False

try:
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import csc_matrix
    SCIPY_OK = True
except ImportError:
    SCIPY_OK = False

try:
    import ctypes
    ctypes.windll.kernel32.SetErrorMode(0x8007)
except Exception:
    pass

try:
    from ortools.sat.python import cp_model
    _test = cp_model.CpModel()
    del _test
    ORTOOLS_OK = True
except Exception:
    ORTOOLS_OK = False

warnings.filterwarnings("ignore")

# ─── File names ──────────────────────────────────────────────── #
# ═══════════════════════════════════════════════════════════════ #
#   SEMESTER CONFIG — change these at the start of every cycle    #
# ═══════════════════════════════════════════════════════════════ #
SEMESTER_LABEL     = "Odd Semester 2026-27 (Nov/Dec 2026 End-Semester)"
# Calendar window shown in the portal (always rendered, even before slots are loaded)
SEMESTER_CAL_START = datetime.date(2026, 11, 1)
SEMESTER_CAL_END   = datetime.date(2026, 12, 31)
# Scholar exam rule: exam day + this many working days before it are blocked
EXAM_BUFFER_DAYS   = 2
# Saturday duty: open to ALL designations this semester (optional / willingness-based).
# TA/RA can be allotted any Saturday (as before); other designations are allotted
# a Saturday ONLY if they themselves selected that Saturday in their willingness.
SAT_ALWAYS_DESIG   = {"TA", "RA"}

FACULTY_FILE      = "Faculty_Master.xlsx"
OFFLINE_FILE      = "Offline_Duty.xlsx"
ONLINE_FILE       = "Online_Duty.xlsx"
WILLINGNESS_FILE  = "Willingness.xlsx"
LOGO_FILE         = "sastra_logo.png"
FINAL_ALLOC_FILE  = "Final_Allocation.xlsx"
ALLOC_REPORT_FILE = "Allocation_Report.xlsx"
GATE_FILE         = "allotment_gate.txt"
PASSWORDS_FILE    = "faculty_passwords.json"

DEFAULT_PASSWORD  = "sastra"   # every new faculty's first-time password
ADMIN_IDS        = {"C2086"}  # Faculty IDs that are always admin

# ─── Designation rules ───────────────────────────────────────── #
# Map raw Excel designation strings → internal codes
DESIG_MAP = {
    # Professor
    "professor":                    "P",
    "prof":                         "P",
    "prof.":                        "P",
    "p":                            "P",
    # Associate Professor
    "acp":                          "ACP",
    "associate professor":          "ACP",
    "assoc. professor":             "ACP",
    "assoc professor":              "ACP",
    # Senior Assistant Professor
    "sap":                          "SAP",
    "senior assistant professor":   "SAP",
    "sr. assistant professor":      "SAP",
    "sr assistant professor":       "SAP",
    # Assistant Professor Grade III / AP3
    "ap 3":                         "AP3",
    "ap3":                          "AP3",
    "ap-3":                         "AP3",
    "ap iii":                       "AP3",
    "assistant professor 3":        "AP3",
    "assistant professor iii":      "AP3",
    "assistant professor grade 3":  "AP3",
    "assistant professor grade iii":"AP3",
    "assistant professor - iii":    "AP3",
    "assistant professor - 3":      "AP3",
    "asst. professor 3":            "AP3",
    "asst professor 3":             "AP3",
    # Assistant Professor Grade II / AP2
    "ap 2":                         "AP2",
    "ap2":                          "AP2",
    "ap-2":                         "AP2",
    "ap ii":                        "AP2",
    "assistant professor 2":        "AP2",
    "assistant professor ii":       "AP2",
    "assistant professor grade 2":  "AP2",
    "assistant professor grade ii": "AP2",
    "assistant professor - ii":     "AP2",
    "assistant professor - 2":      "AP2",
    "asst. professor 2":            "AP2",
    "asst professor 2":             "AP2",
    # Teaching Assistant
    "teaching assistant":           "TA",
    "ta":                           "TA",
    # Research Assistant
    "research assistant":           "RA",
    "ra":                           "RA",
}

def _map_desig(raw: str) -> str:
    """Map a raw designation string to a DESIG_MAP code.
    Falls back to substring/keyword matching before defaulting to TA."""
    s = str(raw).strip().lower()
    # Exact match first
    if s in DESIG_MAP:
        return DESIG_MAP[s]
    # Already a known code (e.g. stored as "P", "ACP" etc.)
    up = s.upper()
    if up in ("P", "ACP", "SAP", "AP3", "AP2", "TA", "RA"):
        return up
    # Keyword fallback
    if "research assistant" in s or s == "ra":
        return "RA"
    if "teaching assistant" in s or s == "ta":
        return "TA"
    if "senior assistant" in s or "sr" in s.split():
        return "SAP"
    if "associate" in s:
        return "ACP"
    if "professor" in s or "prof" in s:
        # Try to detect grade/level
        for token in s.replace("-", " ").split():
            if token in ("3", "iii", "grade3", "gradeiii"):
                return "AP3"
            if token in ("2", "ii", "grade2", "gradeii"):
                return "AP2"
        return "P"   # Plain "professor" → P
    # Last resort
    return "TA"
# Option B: Online duty suspended — all designations use Offline only
DESIG_RULES = {
    "P":   (1, 1, ["Offline"]),   # Online duty suspended this semester
    "ACP": (2, 2, ["Offline"]),   # Both duties now offline
    "SAP": (2, 2, ["Offline"]),
    "AP3": (3, 3, ["Offline"]),
    "AP2": (3, 3, ["Offline"]),
    "TA":  (4, 4, ["Offline"]),   # 4 duties this semester (overridden per-faculty below)
    "RA":  (4, 4, ["Offline"]),
}
DESIG_FULL = {
    "P":   "Professor",
    "ACP": "Associate Professor",
    "SAP": "Senior Assistant Professor",
    "AP3": "Assistant Professor - III",
    "AP2": "Assistant Professor - II",
    "TA":  "Teaching Assistant",
    "RA":  "Research Assistant",
}

# ── Per-faculty designation overrides ───────────────────────────────────────
# Use when the Supabase designation field is NULL/blank/incorrect for a faculty.
# Key = exact faculty name (as stored in Supabase), Value = designation code
# ── Per-faculty valuation date overrides (safety net) ────────────────────────
# Used when Supabase v1-v5 columns are NULL or missing for a faculty.
# Key = exact name as stored in Supabase | Value = set of date strings "YYYY-MM-DD"
FACULTY_VALUATION_OVERRIDE_RAW: dict = {
    # Odd Sem 2026-27: valuation dates to be updated in Supabase (V1..V5).
    # Add entries here only as a fallback, e.g.  "T.Mohanraj": {"2026-12-10"},
}
# ── Per-faculty date cap — duties must be assigned BEFORE this date ──────────
# Key = name substring (without honorifics) | Value = "YYYY-MM-DD" (exclusive upper bound)
FACULTY_DATE_CAP_RAW: dict = {
    # Even Sem 2025-26 entry removed (S. Balamurli, before 15-May-2026)
}

# ── Per-faculty duty count overrides (Odd Sem 2026-27) ───────────────────────
# All other TA/RA: 4 duties, 12 willingness options (via DESIG_RULES / DUTY_STRUCTURE)
FACULTY_DUTY_OVERRIDE_RAW: dict = {
    "MOHAMMED SAID, UY":   3,   # RS799
    "Shri. P. Vijay Guru": 3,   # RS937
}
# Willingness options to select, per faculty (overrides DUTY_STRUCTURE)
FACULTY_WILL_OVERRIDE_RAW: dict = {
    "MOHAMMED SAID, UY":   9,   # RS799 — 3 duties
    "Shri. P. Vijay Guru": 9,   # RS937 — 3 duties
}

# ── Forced date assignments (specific faculty MUST get these slots) ─────────
# Key = name substring as stored in Supabase (without honorifics)
# Value = list of (YYYY-MM-DD, session) tuples
FORCED_ASSIGNMENTS_RAW: dict = {
    # Even Sem 2025-26 entries (Mustafa / Jeyaraj, 10-11 Jun 2026) removed.
    # Example:  "Name": [("2026-11-16", "FN")],
}

# Antony (Shri S. Antony) gets 2 Saturday duties; total duties = 4
# All other SAT_PREASSIGN faculty get 1 Saturday each (19 faculty)
# Antony's 2nd Saturday makes total Saturday coverage = 20
ANTONY_NORM_NAME = "s. antony"   # _norm_name("Shri S. Antony")

# Supabase already has correct values. This overrides at app level as backup.
# Key = exact name as stored in Supabase | Value = designation code
FACULTY_DESIG_OVERRIDE_RAW: dict = {
    "Dr. Anjan Kumar Dash": "P",   # faculty_id C870 — DB already has 'professor'
    # Add more if needed: "Name": "ACP"
}
DUTY_STRUCTURE = {"P": 3, "ACP": 6, "SAP": 6, "AP3": 9, "AP2": 9, "TA": 12, "RA": 12}

# ── Willingness match scores ──────────────────────────────────── #
W_EXACT      = 100_000
W_ACP_ONLINE =  80_000
W_FLIP       =  60_000
W_ADJ1       =  40_000
W_ADJ2       =  20_000
W_VAL_ADJ    =   5_000
W_NON_SUB    =     100
PENALTY      =      10

DESIG_PRIORITY = {
    "P":   6_000_000,
    "ACP": 5_000_000,
    "SAP": 4_000_000,
    "AP3": 3_000_000,
    "AP2": 2_000_000,
    "TA":        0,
    "RA":        0,
}

WILL_TAGS = {
    "Willingness-Exact", "Willingness-ACPOnline",
    "Willingness-SessionFlip", "Willingness-±1Day",
    "Willingness-±2Day", "Willingness-ValAdj",
    "SAP-OnlineFallback"
}

# ─── Page config ─────────────────────────────────────────────── #
st.set_page_config(page_title="SASTRA Duty Portal", layout="wide")
st.markdown("""
<style>
.stApp{background:#f4f7fb}
.main .block-container{max-width:1200px;padding-top:1.2rem;padding-bottom:1.5rem}
.card{background:linear-gradient(180deg,#fff 0%,#f8fafc 100%);border:1px solid #dbe3ef;
      border-radius:14px;padding:16px 18px;box-shadow:0 10px 24px rgba(15,23,42,.08);margin-bottom:12px}
.panel{background:#fff;border:1px solid #e2e8f0;border-radius:14px;
       padding:14px 16px;box-shadow:0 8px 20px rgba(15,23,42,.06);margin-bottom:10px}
.card-title{font-size:1.08rem;font-weight:700;color:#0f172a;margin-bottom:.2rem}
.card-sub{font-size:.93rem;color:#334155;margin-bottom:0}
.sec-title{font-size:1rem;font-weight:700;color:#0b3a67;margin-bottom:.35rem}
.stButton>button{border-radius:10px;border:1px solid #cbd5e1;font-weight:600}
.stDownloadButton>button{border-radius:10px;font-weight:600}
.blink{font-weight:700;color:#800000;padding:10px 12px;border:2px solid #800000;
       background:#fffaf5;border-radius:6px;animation:pulse 2.4s ease-in-out infinite}
@keyframes pulse{0%{opacity:1}50%{opacity:.35}100%{opacity:1}}
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#               SUPABASE CLIENT                                  #
# ═══════════════════════════════════════════════════════════════ #
@st.cache_resource
def _sb() -> Client:
    return create_client(st.secrets["SUPABASE_URL"], st.secrets["SUPABASE_KEY"])

# ── DB helpers ────────────────────────────────────────────────── #
def db_get_faculty_by_id(fid: str):
    r = _sb().table("faculty").select("*").eq("faculty_id", _norm_id(fid)).execute()
    return r.data[0] if r.data else None

def db_get_faculty_by_email(email: str):
    r = _sb().table("faculty").select("*").eq("email", email.strip().lower()).execute()
    return r.data[0] if r.data else None

def db_get_all_faculty():
    r = _sb().table("faculty").select("*").order("name").execute()
    return r.data or []

def db_update_password(fid: str, h: str, must_change: bool = False):
    _sb().table("faculty").update({"password_hash": h, "must_change_pw": must_change}).eq("faculty_id", fid).execute()

def db_reset_faculty_pw(fid: str):
    h = hash_password(DEFAULT_PASSWORD)
    _sb().table("faculty").update({"password_hash": h, "must_change_pw": True}).eq("faculty_id", _norm_id(fid)).execute()

def db_set_admin(fid: str, val: bool):
    _sb().table("faculty").update({"is_admin": val}).eq("faculty_id", _norm_id(fid)).execute()

def db_create_reset_token(fid: str) -> str:
    import secrets as _sec
    token = _sec.token_urlsafe(32)
    exp   = (datetime.datetime.utcnow() + datetime.timedelta(hours=24)).isoformat()
    _sb().table("password_reset_tokens").insert({"faculty_id": fid, "token": token, "expires_at": exp}).execute()
    return token

def db_validate_reset_token(token: str):
    r = _sb().table("password_reset_tokens").select("*").eq("token", token).eq("used", False).execute()
    if not r.data: return None
    row = r.data[0]
    exp = row["expires_at"].replace("Z","").split(".")[0]
    if datetime.datetime.utcnow() > datetime.datetime.fromisoformat(exp): return None
    return row

def db_consume_reset_token(token: str):
    _sb().table("password_reset_tokens").update({"used": True}).eq("token", token).execute()

def _in_semester_window(v) -> bool:
    try:
        d = parse_date_safe(v)
        return pd.notna(d) and SEMESTER_CAL_START <= d.date() <= SEMESTER_CAL_END
    except Exception:
        return False

def db_get_offline_slots():
    """Offline slots for the CURRENT semester only (Nov–Dec 2026).
    Old-semester rows still in Supabase (e.g. May/Jun 2026) are ignored everywhere:
    calendar, date selector, exam-period banner and optimizer."""
    r = _sb().table("offline_duty").select("*").execute()
    return [row for row in (r.data or []) if _in_semester_window(row.get("duty_date"))]

def db_get_online_slots():
    return []          # No online duty this semester

def db_get_all_willingness_rows():
    r = _sb().table("willingness").select("*").order("faculty_name").execute()
    return r.data or []

def db_get_willingness_for(fid: str):
    r = _sb().table("willingness").select("*").eq("faculty_id", fid).execute()
    return r.data or []

def db_already_submitted(fid: str) -> bool:
    r = _sb().table("willingness").select("id").eq("faculty_id", fid).execute()
    return bool(r.data)

def db_submit_willingness(fid: str, faculty_name: str, slots: list):
    _sb().table("willingness").delete().eq("faculty_id", fid).execute()
    def _to_iso(d):
        # slots["Date"] is a python date object from selectbox
        if hasattr(d, "strftime"):
            return d.strftime("%Y-%m-%d")
        # fallback: parse string in any format → ISO
        return to_dt(str(d)).strftime("%Y-%m-%d")
    rows = [{"faculty_id": fid, "faculty_name": faculty_name,
             "duty_date": _to_iso(s["Date"]), "session": s["Session"]} for s in slots]
    if rows: _sb().table("willingness").insert(rows).execute()

def _db_count(table: str, **eq) -> int:
    q = _sb().table(table).select("*", count="exact")
    for k, v in eq.items():
        q = q.eq(k, v)
    r = q.limit(1).execute()
    return int(r.count or 0)

def _db_delete_all(table: str) -> int:
    """Delete every row of `table`. Works whether `id` is an integer or a UUID.
    Returns the number of rows STILL present afterwards (0 = success).
    A non-zero result almost always means Supabase Row Level Security has no
    DELETE policy for this key — Supabase then silently deletes nothing."""
    _sb().table(table).delete().not_.is_("id", "null").execute()
    return _db_count(table)

def db_clear_all_willingness() -> int:
    return _db_delete_all("willingness")

def db_delete_willingness_for(fid: str) -> int:
    """Delete one faculty's willingness. Returns rows still present (0 = success)."""
    _sb().table("willingness").delete().eq("faculty_id", fid).execute()
    return _db_count("willingness", faculty_id=fid)

def db_clear_allocation() -> int:
    return _db_delete_all("final_allocation")

_RLS_HELP = (
    "Supabase did not delete the rows — this is a Row Level Security (RLS) block, "
    "not an app error. Fix once in Supabase → SQL Editor:\n\n"
    "```sql\n"
    "create policy \"admin delete willingness\" on willingness for delete using (true);\n"
    "create policy \"admin delete allocation\"  on final_allocation for delete using (true);\n"
    "```\n"
    "Or put the **service_role** key in SUPABASE_KEY (Streamlit secrets)."
)

def db_save_allocation(records: list):
    _db_delete_all("final_allocation")
    if records: _sb().table("final_allocation").insert(records).execute()

def db_get_allocation_for(fid: str):
    r = _sb().table("final_allocation").select("*").eq("faculty_id", fid).order("duty_date").execute()
    return r.data or []

def db_get_all_allocation():
    r = _sb().table("final_allocation").select("*").order("duty_date").execute()
    return r.data or []

# ═══════════════════════════════════════════════════════════════ #
#        DUTY SWAP — MUTUAL ADJUSTMENT (admin-approved)           #
# ═══════════════════════════════════════════════════════════════ #
SWAP_OPEN_STATUSES = ("pending_partner", "pending_admin")
SWAP_STATUS_LABEL = {
    "pending_partner": "⏳ Waiting for partner",
    "pending_admin":   "🕒 Waiting for approval",
    "approved":        "✅ Approved — allotment updated",
    "declined":        "❌ Declined by partner",
    "rejected":        "⛔ Rejected by admin",
    "cancelled":       "↩ Cancelled by requester",
    "superseded":      "↪ Closed (duty changed by another swap)",
}
SWAP_LEVEL_LABEL = {
    "perfect":  "🟢 Perfect match",
    "good":     "🟡 Good match",
    "possible": "⚪ Possible",
}
SWAP_TABLE_SQL = """create table if not exists duty_swaps (
  id                   bigint generated always as identity primary key,
  created_at           timestamptz default now(),
  requester_id         text,  requester_name text,
  req_alloc_id         text,  req_date date,  req_session text,
  partner_id           text,  partner_name text,
  partner_alloc_id     text,  partner_date date,  partner_session text,
  match_level          text,
  status               text default 'pending_admin',
  partner_responded_at timestamptz,
  admin_decided_at     timestamptz,
  admin_note           text
);
-- Needed only if Row Level Security is ON for these tables:
create policy "swap read"   on duty_swaps for select using (true);
create policy "swap insert" on duty_swaps for insert with check (true);
create policy "swap update" on duty_swaps for update using (true);
create policy "alloc update" on final_allocation for update using (true);"""

def db_swaps_all() -> list:
    r = _sb().table("duty_swaps").select("*").order("id", desc=True).execute()
    return r.data or []

def db_swap_create(rec: dict):
    _sb().table("duty_swaps").insert(rec).execute()

def db_swap_update(swap_id, fields: dict):
    _sb().table("duty_swaps").update(fields).eq("id", swap_id).execute()

def _now_iso() -> str:
    return datetime.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"

def _alloc_date(row):
    d = parse_date_safe(row.get("duty_date"))
    return d.date() if pd.notna(d) else None

def _swap_people(fac_df) -> dict:
    """fid → {name, desig, blocked:set(dates)} — valuation + scholar exam/buffer + lab."""
    people = {}
    for _, fr in fac_df.iterrows():
        fid = _norm_id(fr.get("ID No.", ""))
        nm  = str(fr.get("Name", "")).strip()
        if not fid:
            continue
        blocked = set(valuation_dates_for(fr, nm))
        blocked |= FACULTY_BLACKOUT_CLEAN.get(_exam_key(nm), set())
        people[fid] = {"name": nm, "desig": str(fr.get("Designation", "")), "blocked": blocked}
    return people

def _busy_dates(allocs: list) -> dict:
    """fid → {date: [alloc ids]}"""
    busy = {}
    for a in allocs:
        d = _alloc_date(a)
        if d:
            busy.setdefault(_norm_id(a.get("faculty_id", "")), {}).setdefault(d, []).append(str(a.get("id")))
    return busy

def _can_take(fid, d, people, busy, giving_away_id) -> bool:
    """Can `fid` take a duty on date d, after giving away alloc `giving_away_id`?"""
    p = people.get(fid)
    if p is None or d in p["blocked"]:
        return False
    others = [i for i in busy.get(fid, {}).get(d, []) if i != str(giving_away_id)]
    return not others            # max one duty per day

def _locked_alloc_ids(swaps: list) -> set:
    ids = set()
    for s in swaps:
        if s.get("status") in SWAP_OPEN_STATUSES:
            ids.add(str(s.get("req_alloc_id"))); ids.add(str(s.get("partner_alloc_id")))
    return ids

def _will_by_fid() -> dict:
    out = {}
    for r in db_get_all_willingness_rows():
        d = parse_date_safe(r.get("duty_date"))
        if pd.notna(d):
            out.setdefault(_norm_id(r.get("faculty_id", "")), set()).add(
                (d.date(), str(r.get("session", "")).strip().upper()))
    return out

def swap_candidates(my_fid, my_alloc, allocs, people, swaps, will) -> list:
    """Easy-match list for one of my duties. Every result is rule-valid both ways."""
    me    = _norm_id(my_fid)
    d1    = _alloc_date(my_alloc)
    s1    = str(my_alloc.get("session", "")).strip().upper()
    today = datetime.date.today()
    busy  = _busy_dates(allocs)
    lock  = _locked_alloc_ids(swaps)
    rank  = {"perfect": 0, "good": 1, "possible": 2}
    out = []
    for a in allocs:
        b  = _norm_id(a.get("faculty_id", ""))
        d2 = _alloc_date(a)
        s2 = str(a.get("session", "")).strip().upper()
        if b == me or d2 is None or d2 <= today or str(a.get("id")) in lock:
            continue
        if d2 == d1 and s2 == s1:
            continue                                   # same slot — nothing to swap
        if not _can_take(b, d1, people, busy, a.get("id")):
            continue                                   # partner can't do my duty
        if not _can_take(me, d2, people, busy, my_alloc.get("id")):
            continue                                   # I can't do partner's duty
        they_want = (d1, s1) in will.get(b, set())
        i_want    = (d2, s2) in will.get(me, set())
        lvl = "perfect" if (they_want and i_want) else "good" if (they_want or i_want) else "possible"
        out.append({"level": lvl, "partner_id": b, "partner_name": people[b]["name"],
                    "partner_desig": people[b]["desig"], "alloc": a, "date": d2, "session": s2,
                    "_k": (rank[lvl], abs((d2 - d1).days), people[b]["name"].lower())})
    return sorted(out, key=lambda x: x["_k"])

def validate_swap(sw, allocs, people) -> str:
    """'' if the swap is still valid on current data, else the reason."""
    by_id = {str(a.get("id")): a for a in allocs}
    ra, pa = by_id.get(str(sw["req_alloc_id"])), by_id.get(str(sw["partner_alloc_id"]))
    if ra is None or pa is None:
        return "One of the duties no longer exists in the allotment."
    rq, pt = _norm_id(sw["requester_id"]), _norm_id(sw["partner_id"])
    if _norm_id(ra.get("faculty_id")) != rq or _norm_id(pa.get("faculty_id")) != pt:
        return "One of the duties has already changed hands."
    busy = _busy_dates(allocs)
    if not _can_take(pt, _alloc_date(ra), people, busy, pa.get("id")):
        return f"{sw['partner_name']} is no longer free / eligible on {_alloc_date(ra):%d-%m-%Y}."
    if not _can_take(rq, _alloc_date(pa), people, busy, ra.get("id")):
        return f"{sw['requester_name']} is no longer free / eligible on {_alloc_date(pa):%d-%m-%Y}."
    return ""

def apply_swap(sw, fac_df) -> str:
    """Admin approval: exchange the two allotment rows. Returns '' on success, else error."""
    allocs = db_get_all_allocation()
    people = _swap_people(fac_df)
    err = validate_swap(sw, allocs, people)
    if err:
        return err
    rq, pt = _norm_id(sw["requester_id"]), _norm_id(sw["partner_id"])
    tag = f"Swap #{sw['id']}"
    _sb().table("final_allocation").update({
        "faculty_id": pt, "faculty_name": people[pt]["name"],
        "designation": people[pt]["desig"], "allocated_by": tag,
    }).eq("id", sw["req_alloc_id"]).execute()
    _sb().table("final_allocation").update({
        "faculty_id": rq, "faculty_name": people[rq]["name"],
        "designation": people[rq]["desig"], "allocated_by": tag,
    }).eq("id", sw["partner_alloc_id"]).execute()
    # verify
    chk = {str(a.get("id")): _norm_id(a.get("faculty_id")) for a in db_get_all_allocation()}
    if chk.get(str(sw["req_alloc_id"])) != pt or chk.get(str(sw["partner_alloc_id"])) != rq:
        return ("Supabase did not save the change (Row Level Security). Run once in SQL Editor: "
                'create policy "alloc update" on final_allocation for update using (true);')
    db_swap_update(sw["id"], {"status": "approved", "admin_decided_at": _now_iso()})
    # close other open requests that involved either duty
    ids = {str(sw["req_alloc_id"]), str(sw["partner_alloc_id"])}
    for o in db_swaps_all():
        if o["id"] != sw["id"] and o.get("status") in SWAP_OPEN_STATUSES and \
           ({str(o.get("req_alloc_id")), str(o.get("partner_alloc_id"))} & ids):
            db_swap_update(o["id"], {"status": "superseded"})
    return ""

def _duty_txt(d, s) -> str:
    d = parse_date_safe(d)
    return f"{d:%d-%m-%Y} ({d:%a}) {str(s).upper()}" if pd.notna(d) else f"{d} {s}"


# ═══════════════════════════════════════════════════════════════ #
#     FINAL ALLOTMENT — admin upload + export for authorities     #
# ═══════════════════════════════════════════════════════════════ #
_DESIG_RANK = {c: i for i, c in enumerate(["P", "ACP", "SAP", "AP3", "AP2", "TA", "RA"])}

def _people_index(fac_df):
    """Lookups to match an uploaded row to a faculty: by ID and by tolerant name key."""
    by_id, by_key = {}, {}
    for _, fr in fac_df.iterrows():
        rec = {"fid": _norm_id(fr.get("ID No.", "")), "name": str(fr.get("Name", "")).strip(),
               "desig": str(fr.get("Designation", ""))}
        if rec["fid"]:
            by_id[rec["fid"]] = rec
        by_key.setdefault(_exam_key(rec["name"]), rec)
    return by_id, by_key

def _find_header(raw: pd.DataFrame):
    """Row index (0-based) whose cells include a Name and a Date heading."""
    for i in range(min(len(raw), 15)):
        cells = [str(v).strip().upper() for v in raw.iloc[i].tolist()]
        if any("NAME" in c for c in cells) and any("DATE" in c for c in cells):
            return i
    return None

def parse_final_allotment(f, fac_df):
    """Read an allotment Excel (the app's own download, the authorities export, or a
    hand-edited copy). Returns (records, errors)."""
    xl = pd.ExcelFile(f)
    order = ([s for s in xl.sheet_names if s.lower() in ("full_allocation", "date-wise")]
             + [s for s in xl.sheet_names if s.lower() not in ("full_allocation", "date-wise")])
    df = None
    for sh in order:
        raw = pd.read_excel(xl, sheet_name=sh, header=None, dtype=object)
        h = _find_header(raw)
        if h is None:
            continue
        cand = pd.read_excel(xl, sheet_name=sh, header=h, dtype=object)
        cand.columns = [str(c).strip() for c in cand.columns]
        if any("SESS" in c.upper() for c in cand.columns):
            df = cand
            break
    if df is None:
        return [], ["No sheet with Name, Date and Session columns was found."]
    up = {c: c.upper() for c in df.columns}
    c_name = next((c for c in df.columns if "NAME" in up[c]), None)
    c_id   = next((c for c in df.columns if ("ID" in up[c] and "MAIL" not in up[c]) or "CODE" in up[c]), None)
    c_date = next((c for c in df.columns if "DATE" in up[c]), None)
    c_sess = next((c for c in df.columns if "SESS" in up[c]), None)
    c_type = next((c for c in df.columns if up[c] in ("TYPE", "MODE", "DUTY TYPE")), None)
    by_id, by_key = _people_index(fac_df)
    recs, errs = [], []
    for i, r in df.iterrows():
        nm = str(r.get(c_name, "") if c_name else "").strip()
        fid = _norm_id(r.get(c_id, "")) if c_id else ""
        if (not nm or nm.lower() == "nan") and (not fid or fid == "NAN"):
            continue                                            # blank row
        d = parse_date_safe(r.get(c_date))
        sn = normalize_session(r.get(c_sess, ""))
        if pd.isna(d) or sn not in ("FN", "AN"):
            errs.append(f"Row {i + 2}: {nm or fid} — date or session not readable "
                        f"('{r.get(c_date)}', '{r.get(c_sess)}').")
            continue
        p = by_id.get(fid) if fid and fid != "NAN" else None
        p = p or by_key.get(_exam_key(nm))
        if p is None:
            errs.append(f"Row {i + 2}: '{nm or fid}' not found in the faculty list.")
            continue
        recs.append({
            "faculty_id": p["fid"], "faculty_name": p["name"], "designation": p["desig"],
            "duty_date": d.date().isoformat(), "session": sn,
            "duty_type": (str(r.get(c_type)).strip() if c_type and str(r.get(c_type)).strip().lower()
                          not in ("", "nan") else "Offline"),
            "allocated_by": "Final (admin upload)",
        })
    return recs, errs

def check_allotment(recs, fac_df, offline_df) -> dict:
    """Rule check of an allotment. Returns {'errors': [...], 'warnings': [...]}."""
    errors, warns = [], []
    people = _swap_people(fac_df)
    seen, per_day, per_fac, per_slot = set(), {}, {}, {}
    for r in recs:
        k = (r["faculty_id"], r["duty_date"], r["session"])
        if k in seen:
            errors.append(f"{r['faculty_name']} is listed twice on {_duty_txt(r['duty_date'], r['session'])}.")
        seen.add(k)
        per_day.setdefault((r["faculty_id"], r["duty_date"]), []).append(r["session"])
        per_fac[r["faculty_id"]] = per_fac.get(r["faculty_id"], 0) + 1
        per_slot[(r["duty_date"], r["session"])] = per_slot.get((r["duty_date"], r["session"]), 0) + 1
        d = parse_date_safe(r["duty_date"]).date()
        if not (SEMESTER_CAL_START <= d <= SEMESTER_CAL_END):
            errors.append(f"{r['faculty_name']}: {d:%d-%m-%Y} is outside the exam period.")
        p = people.get(r["faculty_id"])
        if p and d in p["blocked"]:
            warns.append(f"{r['faculty_name']} has duty on a blocked date "
                         f"(valuation / exam / lab): {_duty_txt(r['duty_date'], r['session'])}.")
    for (fid, dd), ss in per_day.items():
        if len(ss) > 1:
            warns.append(f"{people.get(fid, {}).get('name', fid)} has both FN and AN on "
                         f"{parse_date_safe(dd):%d-%m-%Y}.")
    # session requirement
    if offline_df is not None and not offline_df.empty:
        req = (offline_df.assign(_d=offline_df["Date"].dt.date.astype(str),
                                 _s=offline_df["Session"].astype(str).str.upper())
               .groupby(["_d", "_s"])["Required"].sum().to_dict())
        for (dd, ss), n in sorted(req.items()):
            got = per_slot.get((dd, ss), 0)
            if got != int(n):
                warns.append(f"{_duty_txt(dd, ss)}: required {int(n)}, allotted {got}.")
        for (dd, ss), got in sorted(per_slot.items()):
            if (dd, ss) not in req:
                warns.append(f"{_duty_txt(dd, ss)}: {got} allotted, but this session is not in the duty schedule.")
    # per-faculty count
    for _, fr in fac_df.iterrows():
        fid = _norm_id(fr.get("ID No.", "")); nm = str(fr.get("Name", "")).strip()
        need = fac_duty_range(nm, str(fr.get("Designation", "")))[0]
        got = per_fac.get(fid, 0)
        if need and got != need:
            warns.append(f"{nm} ({fid}): expected {need} duties, allotted {got}.")
    return {"errors": errors, "warnings": warns}

def build_authority_excel(allocs: list, fac_rows: list, offline_df=None) -> bytes:
    """Formatted final allotment for the authorities — faculty + research scholars together."""
    from openpyxl import Workbook
    from openpyxl.styles import Font, Alignment, PatternFill, Border, Side
    from openpyxl.utils import get_column_letter
    F  = "Arial"
    thin = Side(style="thin", color="999999")
    box  = Border(left=thin, right=thin, top=thin, bottom=thin)
    hdr_fill = PatternFill("solid", fgColor="1E3A5F")
    alt_fill = PatternFill("solid", fgColor="F1F5F9")
    titles = ["SASTRA Deemed University — School of Mechanical Engineering",
              f"Invigilation Duty Allotment — {SEMESTER_LABEL}",
              f"Generated on {datetime.date.today():%d-%m-%Y}"]

    fac = {}
    for r in fac_rows:
        code = _map_desig(r.get("designation", ""))
        fac[_norm_id(r.get("faculty_id", ""))] = {
            "name": " ".join(str(r.get("name", "")).split()), "code": code,
            "desig": DESIG_FULL.get(code, code)}
    duties = {}
    for a in allocs:
        fid = _norm_id(a.get("faculty_id", ""))
        d = parse_date_safe(a.get("duty_date"))
        if pd.isna(d):
            continue
        duties.setdefault(fid, []).append((d.date(), str(a.get("session", "")).upper()))
        if fid not in fac:
            code = _map_desig(a.get("designation", ""))
            fac[fid] = {"name": " ".join(str(a.get("faculty_name", "")).split()), "code": code,
                        "desig": DESIG_FULL.get(code, code)}
    order = sorted(fac, key=lambda f: (_DESIG_RANK.get(fac[f]["code"], 99), fac[f]["name"].lower()))

    def _sheet(ws, header, rows, widths):
        ncol = len(header)
        for i, t in enumerate(titles, start=1):
            ws.cell(row=i, column=1, value=t).font = Font(name=F, bold=(i < 3), size=(13 if i == 1 else 11))
            ws.merge_cells(start_row=i, start_column=1, end_row=i, end_column=ncol)
            ws.cell(row=i, column=1).alignment = Alignment(horizontal="center")
        hr = len(titles) + 2
        for j, h in enumerate(header, start=1):
            c = ws.cell(row=hr, column=j, value=h)
            c.font = Font(name=F, bold=True, color="FFFFFF"); c.fill = hdr_fill; c.border = box
            c.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)
        for i, row in enumerate(rows):
            for j, v in enumerate(row, start=1):
                c = ws.cell(row=hr + 1 + i, column=j, value=v)
                c.font = Font(name=F); c.border = box
                c.alignment = Alignment(vertical="center", wrap_text=True)
                if i % 2:
                    c.fill = alt_fill
        for j, w in enumerate(widths, start=1):
            ws.column_dimensions[get_column_letter(j)].width = w
        ws.freeze_panes = ws.cell(row=hr + 1, column=1)
        ws.print_title_rows = f"{hr}:{hr}"
        ws.page_setup.orientation = "landscape"
        ws.page_setup.fitToWidth = 1; ws.page_setup.fitToHeight = 0
        ws.sheet_properties.pageSetUpPr.fitToPage = True

    wb = Workbook()
    # Sheet 1 — faculty-wise
    maxd = max([len(v) for v in duties.values()] + [1])
    ws = wb.active; ws.title = "Faculty-wise"
    rows = []
    for n, fid in enumerate(order, start=1):
        ds = sorted(duties.get(fid, []))
        rows.append([n, fid, fac[fid]["name"], fac[fid]["desig"], len(ds)]
                    + [f"{d:%d-%m-%Y} ({d:%a}) {s}" for d, s in ds] + [""] * (maxd - len(ds)))
    _sheet(ws, ["Sl.No", "ID No.", "Name", "Designation", "No. of Duties"]
               + [f"Duty {i}" for i in range(1, maxd + 1)],
           rows, [7, 10, 32, 24, 10] + [22] * maxd)
    # Sheet 2 — date-wise
    ws2 = wb.create_sheet("Date-wise")
    flat = sorted([(d, 0 if s == "FN" else 1, s, fid) for fid, v in duties.items() for d, s in v],
                  key=lambda x: (x[0], x[1], _DESIG_RANK.get(fac[x[3]]["code"], 99), fac[x[3]]["name"].lower()))
    _sheet(ws2, ["Sl.No", "Date", "Day", "Session", "ID No.", "Name", "Designation"],
           [[i, f"{d:%d-%m-%Y}", f"{d:%A}", s, fid, fac[fid]["name"], fac[fid]["desig"]]
            for i, (d, _o, s, fid) in enumerate(flat, start=1)],
           [7, 12, 12, 9, 10, 32, 24])
    # Sheet 3 — session summary
    ws3 = wb.create_sheet("Session Summary")
    cnt = {}
    for d, _o, s, _f in flat:
        cnt[(d, s)] = cnt.get((d, s), 0) + 1
    req = {}
    if offline_df is not None and not offline_df.empty:
        for _, r in offline_df.iterrows():
            req[(r["Date"].date(), str(r["Session"]).upper())] = \
                req.get((r["Date"].date(), str(r["Session"]).upper()), 0) + int(r["Required"])
    keys = sorted(set(cnt) | set(req), key=lambda k: (k[0], 0 if k[1] == "FN" else 1))
    _sheet(ws3, ["Sl.No", "Date", "Day", "Session", "Required", "Allotted", "Status"],
           [[i, f"{d:%d-%m-%Y}", f"{d:%A}", s, req.get((d, s), ""), cnt.get((d, s), 0),
             ("OK" if req.get((d, s)) == cnt.get((d, s), 0) else "Check") if req else ""]
            for i, (d, s) in enumerate(keys, start=1)]
           + [["", "", "", "Total", sum(req.values()) if req else "", sum(cnt.values()), ""]],
           [7, 12, 12, 9, 10, 10, 9])
    bio = io.BytesIO(); wb.save(bio)
    return bio.getvalue()


def db_get_setting(key: str, default: str = "") -> str:
    # Try session state cache first (avoids a DB round-trip and works even if table missing)
    _ss_key = f"_setting_{key}"
    if _ss_key in st.session_state:
        return st.session_state[_ss_key]
    try:
        r = _sb().table("portal_settings").select("value").eq("key", key).execute()
        val = r.data[0]["value"] if r.data else default
        st.session_state[_ss_key] = val
        return val
    except Exception:
        return default

def db_set_setting(key: str, value: str):
    # Always update session-state cache so the UI reflects the change immediately
    st.session_state[f"_setting_{key}"] = value
    try:
        # Try upsert with explicit conflict column first (requires 'key' to be PK/unique)
        _sb().table("portal_settings").upsert(
            {"key": key, "value": value},
            on_conflict="key"
        ).execute()
    except Exception:
        try:
            # Fallback: delete then insert
            _sb().table("portal_settings").delete().eq("key", key).execute()
            _sb().table("portal_settings").insert({"key": key, "value": value}).execute()
        except Exception:
            # Table may not exist — setting is preserved in session state only
            pass


# ═══════════════════════════════════════════════════════════════ #
#                   ALLOTMENT GATE                               #
# ═══════════════════════════════════════════════════════════════ #
def gate_is_open() -> bool:
    return db_get_setting("allotment_gate", "0") == "1"

def set_gate(open_: bool):
    db_set_setting("allotment_gate", "1" if open_ else "0")


# ═══════════════════════════════════════════════════════════════ #
#              PASSWORD HELPERS (bcrypt)                         #
# ═══════════════════════════════════════════════════════════════ #
def hash_password(plain: str) -> str:
    if BCRYPT_OK:
        return bcrypt.hashpw(plain.encode(), bcrypt.gensalt()).decode()
    # Fallback: SHA-256 prefixed (insecure, encourages installing bcrypt)
    import hashlib
    return "sha256:" + hashlib.sha256(plain.encode()).hexdigest()

def verify_password(plain: str, hashed: str) -> bool:
    if not hashed:
        return False
    try:
        if hashed.startswith("sha256:"):
            import hashlib
            return hashed == "sha256:" + hashlib.sha256(plain.encode()).hexdigest()
        if BCRYPT_OK:
            return bcrypt.checkpw(plain.encode(), hashed.encode())
    except Exception:
        pass
    return False


# ═══════════════════════════════════════════════════════════════ #
#           PASSWORD HELPERS (Supabase-backed)                   #
# ═══════════════════════════════════════════════════════════════ #
def _norm_id(fid: str) -> str:
    return str(fid).strip().upper().replace(" ", "")

def pw_get(fid: str) -> dict | None:
    """Return faculty row from Supabase as password-compatible dict."""
    row = db_get_faculty_by_id(fid)
    if not row: return None
    return {"password_hash": row["password_hash"],
            "must_change_pw": row.get("must_change_pw", True),
            "is_admin": row.get("is_admin", False)}

def pw_ensure(fid: str):
    """No-op: faculty are pre-loaded via load_to_supabase.py."""
    pass

def pw_update(fid: str, new_hash: str, must_change: bool = False):
    db_update_password(_norm_id(fid), new_hash, must_change)

def pw_reset(fid: str):
    db_reset_faculty_pw(_norm_id(fid))

def pw_set_admin(fid: str, is_admin: bool):
    db_set_admin(_norm_id(fid), is_admin)

def pw_ensure_all(id_list: list):
    """No-op: faculty are pre-loaded via load_to_supabase.py."""
    pass


# ═══════════════════════════════════════════════════════════════ #
#                     UTILITY FUNCTIONS                          #
# ═══════════════════════════════════════════════════════════════ #
def clean(x):
    return str(x).strip().lower()

# Honorific prefixes to strip for robust name matching
_HONORIFICS = {"shri", "shri.", "ms", "ms.", "mr", "mr.", "dr", "dr.", "prof", "prof."}

def _norm_name(name: str) -> str:
    """Lowercase + strip leading honorifics (Shri, Ms, Dr, Prof etc.)
    so that 'Shri C. Frizil Kinsly' and 'C. Frizil Kinsly' both → 'c. frizil kinsly'."""
    parts = clean(name).split()
    while parts and parts[0].rstrip('.') in _HONORIFICS:
        parts = parts[1:]
    return " ".join(parts)

# Build clean-keyed lookup after clean() is available
FACULTY_DESIG_OVERRIDE = {_norm_name(k): v for k, v in FACULTY_DESIG_OVERRIDE_RAW.items()}

# Build date cap lookup
FACULTY_DATE_CAP: dict = {
    _norm_name(k): datetime.date.fromisoformat(v)
    for k, v in FACULTY_DATE_CAP_RAW.items()
}

# Build duty override lookup
FACULTY_DUTY_OVERRIDE: dict = {
    _norm_name(k): v for k, v in FACULTY_DUTY_OVERRIDE_RAW.items()
}
FACULTY_WILL_OVERRIDE: dict = {
    _norm_name(k): v for k, v in FACULTY_WILL_OVERRIDE_RAW.items()
}

# Build forced assignments with _norm_name keys and parsed dates
import datetime as _dt_mod
FORCED_ASSIGNMENTS: dict = {
    _norm_name(k): [
        {"date": _dt_mod.date.fromisoformat(d), "session": s, "type": "Offline"}
        for d, s in v
    ]
    for k, v in FORCED_ASSIGNMENTS_RAW.items()
}
del _dt_mod

# Build valuation override with _norm_name keys
FACULTY_VALUATION_OVERRIDE = {
    _norm_name(k): {pd.Timestamp(d).date() for d in v}
    for k, v in FACULTY_VALUATION_OVERRIDE_RAW.items()
}

# ── TA/RA duty-count group (4 or 5 duties, may select Saturday dates) ── #
_SAT_PREASSIGN_RAW: list = []   # Even Sem 2025-26 group retired; TA/RA now follow DESIG_RULES
SAT_PREASSIGN_CLEAN = {_norm_name(n) for n in _SAT_PREASSIGN_RAW}

# Faculty receiving 5 duties; all others in the list get 4 duties
_FIVE_DUTY_RAW: list = []   # none this semester
FIVE_DUTY_CLEAN = {_norm_name(n) for n in _FIVE_DUTY_RAW}

# Per-faculty exam dates — Research Scholars Course Work, Odd Sem 2026-27
# Source: Research_Scholars_Course_Work_details (odd sem 26-27).xlsx
# Scholars with "NA" for all exam dates are not listed.
def _exam_key(name: str) -> str:
    """Tolerant name key for exam-date lookups: honorifics stripped, then only
    letters kept, so 'Shri V.Gladstone' == 'V. Gladstone' == 'v gladstone'."""
    return "".join(ch for ch in _norm_name(name) if ch.isalpha())

_D = datetime.date
_FACULTY_EXAM_DATES_RAW: dict = {
    "Shri V.Gladstone":       {_D(2026, 11, 25)},                                     # RS1007
    "Shri N. Arun Kumar":     {_D(2026, 11, 25)},                                     # RS1063
    "S. Smrithika":           {_D(2026, 11, 20)},                                     # RS1092
    "V. Ramesh Srenyvasan":   {_D(2026, 11, 14)},                                     # RS1155
    "P. Panneerselvam":       {_D(2026, 11, 19)},                                     # RS1197
    "S. Sabrish":             {_D(2026, 11, 23), _D(2026, 11, 30)},                   # RS1222
    "C. Frizil Kinsly":       {_D(2026, 11, 19)},                                     # RS1232
    "S. Manikandan":          {_D(2026, 11, 14), _D(2026, 11, 17), _D(2026, 11, 23)}, # RS1233
    "Shri I.Ilam Parithi":    {_D(2026, 11, 14), _D(2026, 11, 19), _D(2026, 11, 25)}, # RS1302
    "R. PRABHURAJ":           {_D(2026, 11, 19), _D(2026, 11, 25)},                   # RS1322
}
del _D
FACULTY_EXAM_DATES_CLEAN: dict = {
    _exam_key(k): v for k, v in _FACULTY_EXAM_DATES_RAW.items()
}

def _prev_working_day(d: datetime.date, steps: int) -> datetime.date:
    """Return the date `steps` working days before d (skips Sundays only, Sat allowed for duty)."""
    cur = d
    for _ in range(steps):
        cur -= datetime.timedelta(days=1)
        while cur.weekday() == 6:   # skip Sundays only
            cur -= datetime.timedelta(days=1)
    return cur

def _expand_exam_blackout(exam_dates: set, buffer: int = EXAM_BUFFER_DAYS) -> set:
    """Return exam_dates expanded with n-1 and n-2 working days before each exam date."""
    expanded = set(exam_dates)
    for d in exam_dates:
        for step in range(1, buffer + 1):
            expanded.add(_prev_working_day(d, step))
    return expanded

# Lab examination duty — MEC103 Engineering Practices Laboratory (Odd Sem 2026-27)
# Source: EPL_Lab_Exam_Timetable.pdf. The whole lab-exam day is blocked (FN + AN);
# no buffer days. Names are as in the faculty master list.
_D = datetime.date
_FACULTY_LAB_DATES_RAW: dict = {
    "Dr. S. Ramesh":             {_D(2026, 11, 30), _D(2026, 12, 3)},   # C1087
    "Shri M. Tagore":            {_D(2026, 11, 30), _D(2026, 12, 4)},   # C1715
    "Dr. K. Palaksha Reddy":     {_D(2026, 11, 30)},                    # C1591
    "Dr. S. Krishnamani":        {_D(2026, 11, 30)},                    # C1903
    "Shri J. Hari Vignesh":      {_D(2026, 12, 1), _D(2026, 12, 4)},    # C1789
    "Dr. P.S. Sivasakthivel":    {_D(2026, 12, 1)},                     # C2210
    "Dr. C.B. Maheswaran":       {_D(2026, 12, 1)},                     # C1840
    "Dr. D.Venkatesan":          {_D(2026, 12, 1)},                     # C1606
    "Dr. K. Thiruppathi":        {_D(2026, 12, 2)},                     # C809
    "Dr. S. Ramesh Kumar":       {_D(2026, 12, 2)},                     # C2020
    "Dr. G. Rajamohan":          {_D(2026, 12, 2)},                     # C2191
    "Dr. Naveen Kumar A":        {_D(2026, 12, 2)},                     # C2620 (timetable: A. Naveen Kumar)
    "Shri R. Jayendra Bharathi": {_D(2026, 12, 3), _D(2026, 12, 4)},    # C1824
    "Dr. T.Ashok Kumar":         {_D(2026, 12, 3), _D(2026, 12, 4)},    # C479
    "Dr. P. Raja":               {_D(2026, 12, 3)},                     # C482
    "Dr. Subin P George":        {_D(2026, 12, 4)},                     # C2571
}
del _D
FACULTY_LAB_DATES_CLEAN: dict = {
    _exam_key(k): v for k, v in _FACULTY_LAB_DATES_RAW.items()
}

# Per-faculty ALLOTMENT blackout =
#   scholar exam dates + n-1, n-2 working days before each exam date
#   + lab examination duty days (no buffer).
# These dates are fully blocked from the willingness selector AND the optimizer.
FACULTY_BLACKOUT_CLEAN: dict = {
    fc: _expand_exam_blackout(dates)
    for fc, dates in FACULTY_EXAM_DATES_CLEAN.items()
}
for _fc, _dates in FACULTY_LAB_DATES_CLEAN.items():
    FACULTY_BLACKOUT_CLEAN.setdefault(_fc, set()).update(_dates)


def fac_duty_range(fn: str, desig: str) -> tuple:
    """Return (min_duties, max_duties) for a faculty member.
    Strips honorifics before matching so Supabase names match correctly."""
    fc = _norm_name(fn)
    # Per-faculty override takes highest priority (0 = excluded, N = extra duties)
    if fc in FACULTY_DUTY_OVERRIDE:
        n = FACULTY_DUTY_OVERRIDE[fc]
        return n, n
    if fc in FIVE_DUTY_CLEAN:
        return 5, 5
    if fc in SAT_PREASSIGN_CLEAN:
        return 4, 4
    dr = DESIG_RULES.get(desig, DESIG_RULES["TA"])
    return dr[0], dr[1]


# ═══════════════════════════════════════════════════════════════ #
#        FACULTY / SCHOLAR LIST SYNC  (Excel → Supabase)          #
# ═══════════════════════════════════════════════════════════════ #
def _find_col(df, *keys, exclude=()):
    for c in df.columns:
        cu = str(c).upper()
        if all(k in cu for k in keys) and not any(x in cu for x in exclude):
            return c
    return None

def parse_faculty_excels(files) -> dict:
    """Read one or more uploaded Excel files and return {faculty_id: {...}}.
    Understands both formats:
      • Faculty list : S.No. | ID No. | NAME OF STAFF | Designation
      • Scholar list : Sl.No | Code | Name | Designation (TA/RA) | Mobile number | Official mail id
    Later files fill in email / mobile for IDs already read."""
    out = {}
    for f in files:
        df = pd.read_excel(f, dtype=str)
        df.columns = [str(c).strip() for c in df.columns]
        c_id   = (_find_col(df, "ID", "NO") or _find_col(df, "CODE")
                  or _find_col(df, "ID", exclude=("MAIL",)))
        c_name = _find_col(df, "NAME")
        c_des  = _find_col(df, "DESIG")
        c_mail = _find_col(df, "MAIL")
        c_mob  = _find_col(df, "MOBILE") or _find_col(df, "PHONE")
        if not (c_id and c_name):
            raise ValueError(f"{getattr(f, 'name', 'file')}: could not find ID/Code and Name columns.")
        for _, r in df.iterrows():
            fid = _norm_id(r.get(c_id, ""))
            nm  = " ".join(str(r.get(c_name, "")).split())
            if not fid or fid in ("NAN", "NONE") or not nm or nm.lower() == "nan":
                continue
            rec = out.setdefault(fid, {"faculty_id": fid})
            rec.setdefault("name", nm)
            if c_des and str(r.get(c_des, "")).strip().lower() not in ("", "nan"):
                rec.setdefault("designation", str(r[c_des]).strip())
            if c_mail and str(r.get(c_mail, "")).strip().lower() not in ("", "nan", "na"):
                rec["email"] = str(r[c_mail]).strip().lower()
            if c_mob and str(r.get(c_mob, "")).strip().lower() not in ("", "nan", "na"):
                rec["mobile"] = str(r[c_mob]).strip().split(".")[0]
    return out

def plan_faculty_sync(new: dict, existing_rows: list) -> dict:
    """Compare Excel vs Supabase. Returns add / update / missing lists."""
    ex = {_norm_id(r["faculty_id"]): r for r in existing_rows}
    cols = set().union(*[set(r.keys()) for r in existing_rows]) if existing_rows else set()
    mob_col = next((c for c in ("mobile", "mobile_number", "phone", "phone_number") if c in cols), None)
    add, upd = [], []
    for fid, rec in new.items():
        fields = {"name": rec["name"]}
        if rec.get("designation"):
            fields["designation"] = rec["designation"]
        if rec.get("email") and (not existing_rows or "email" in cols):
            fields["email"] = rec["email"]
        if rec.get("mobile") and mob_col:
            fields[mob_col] = rec["mobile"]
        if fid not in ex:
            add.append({"faculty_id": fid, **fields})
        else:
            cur = ex[fid]
            diff = {k: v for k, v in fields.items() if str(cur.get(k) or "").strip() != str(v)}
            if diff:
                upd.append({"faculty_id": fid, "old_name": cur.get("name"), **diff})
    missing = [r for k, r in ex.items() if k not in new]
    return {"add": add, "update": upd, "missing": missing}


def parse_slot_excel(f) -> list:
    """Read a duty-slot Excel. Accepts either layout:
      A) Date | Session (FN/AN) | Required
      B) Date | FN | AN          (number of duties in each session)
    Returns [{"duty_date": "YYYY-MM-DD", "session": "FN"/"AN", "required": n}, ...]"""
    df = pd.read_excel(f)
    df.columns = [str(c).strip() for c in df.columns]
    up = {c: c.upper() for c in df.columns}
    c_date = next((c for c in df.columns if "DATE" in up[c]), None)
    c_sess = next((c for c in df.columns if "SESS" in up[c]), None)
    c_req  = next((c for k in ("REQ", "DUT", "COUNT") for c in df.columns
                   if k in up[c] and c not in (c_date, c_sess)), None)
    c_fn   = next((c for c in df.columns if up[c] in ("FN", "FORENOON")), None)
    c_an   = next((c for c in df.columns if up[c] in ("AN", "AFTERNOON")), None)
    if not c_date:
        raise ValueError("No 'Date' column found.")
    out = {}
    def _add(d, sess, n):
        try:
            n = int(float(n))
        except Exception:
            return
        if n > 0:
            key = (d, sess)
            out[key] = out.get(key, 0) + n
    for _, r in df.iterrows():
        d = parse_date_safe(r[c_date])
        if pd.isna(d):
            continue
        d = d.date()
        if c_sess and c_req:
            sn = normalize_session(r[c_sess])
            if sn in ("FN", "AN"):
                _add(d, sn, r[c_req])
        elif c_fn or c_an:
            if c_fn: _add(d, "FN", r[c_fn])
            if c_an: _add(d, "AN", r[c_an])
        else:
            raise ValueError("Need either Session + Required columns, or FN / AN columns.")
    return [{"duty_date": d.isoformat(), "session": sn, "required": n}
            for (d, sn), n in sorted(out.items())]

def normalize_session(v):
    t = str(v).strip().upper()
    if t in {"FN", "FORENOON", "MORNING", "AM"}:
        return "FN"
    if t in {"AN", "AFTERNOON", "EVENING", "PM"}:
        return "AN"
    return t

_ISO_RE = re.compile(r"^\d{4}-\d{1,2}-\d{1,2}")

def parse_date_safe(val):
    """Single date parser for the whole app — never confuses DD-MM with MM-DD.
      • date / datetime / Timestamp objects               → used as-is
      • YYYY-MM-DD (Supabase / ISO, with or without time)  → year-month-day
      • anything else (25-11-2026, 25.11.2026, 25/11/26)   → DAY first
    Note: pd.to_datetime("2026-12-02", dayfirst=True) wrongly gives 12-Feb-2026,
    so the app must never call it with dayfirst on ISO strings."""
    if val is None:
        return pd.NaT
    if isinstance(val, pd.Timestamp):
        return val
    if isinstance(val, (datetime.datetime, datetime.date)):
        return pd.Timestamp(val)
    s = str(val).strip()
    if not s or s.lower() in ("nan", "nat", "none", "na"):
        return pd.NaT
    m = _ISO_RE.match(s)
    if m:
        return pd.to_datetime(m.group(0), format="%Y-%m-%d", errors="coerce")
    s2 = s.split()[0].replace(".", "-").replace("/", "-")
    for fmt in ("%d-%m-%Y", "%d-%m-%y"):
        try:
            return pd.to_datetime(s2, format=fmt)
        except Exception:
            pass
    return pd.to_datetime(s, dayfirst=True, errors="coerce")

def to_dt(x):
    """parse_date_safe for a scalar OR a pandas Series (returns a datetime64 Series)."""
    if isinstance(x, pd.Series):
        return pd.to_datetime(x.map(parse_date_safe), errors="coerce")
    return parse_date_safe(x)

def fmt_day(val):
    dt = to_dt(val)
    return f"{dt.strftime('%d-%m-%Y')} ({dt.strftime('%A')})" if pd.notna(dt) else str(val)

def demand_category(req: int) -> str:
    if req < 3:  return "Low (<3)"
    if req <= 7: return "Medium (3-7)"
    return "High (>7)"

def valuation_dates_for(row, faculty_name: str = ""):
    dates = set()
    for c in ["V1", "V2", "V3", "V4", "V5"]:
        if c not in row.index:
            continue
        val = row[c]
        if val is None or (hasattr(val, '__class__') and val.__class__.__name__ == 'NaTType'):
            continue
        try:
            if pd.isna(val):
                continue
        except Exception:
            pass
        try:
            ts = parse_date_safe(val)   # ISO from Supabase, or DD-MM-YYYY
            if pd.notna(ts):
                dates.add(ts.date())
        except Exception:
            pass
    # Merge fallback override dates (FACULTY_VALUATION_OVERRIDE_RAW)
    fn = _norm_name(faculty_name)
    if fn in FACULTY_VALUATION_OVERRIDE:
        dates |= FACULTY_VALUATION_OVERRIDE[fn]
    return sorted(dates)

def qp_dates_for(row):
    return sorted({
        to_dt(row[c]).strftime("%d-%m-%Y")
        for c in row.index
        if "QP" in str(c).upper()
        and "DATE" in str(c).upper()
        and pd.notna(row[c])
        and pd.notna(to_dt(row[c]))
    })

def fac_mask(df, sel_clean):
    if df.empty:
        return pd.Series([], dtype=bool)
    cols = [c for c in df.columns if "name" in c.lower() or "faculty" in c.lower()]
    mask = pd.Series([False] * len(df), index=df.index)
    for c in cols:
        mask = mask | (df[c].astype(str).apply(clean) == sel_clean)
    return mask

def wa_link(phone, msg):
    p = str(phone).strip().replace("+", "").replace(" ", "").replace("-", "")
    return f"https://wa.me/{p}?text={urllib.parse.quote(msg)}"

def build_msg(name, will, val, inv, qp, match_str="", dev_lines=None):
    lines = [
        f"Dear {name},",
        "",
        "Examination Duty Details — SASTRA SoME:",
        "",
        "1) Invigilation Duty Dates (Final Allotment):",
        *(inv or ["  Not allotted yet"]),
        "",
        "2) Valuation Dates (Full Day):",
        *(val or ["  Not available"]),
        "",
        "3) QP Feedback Dates:",
        *(qp or ["  Please check the faculty webmaster portal"]),
        "",
    ]
    if match_str:
        lines += [
            "4) Willingness Match Summary:",
            f"   {match_str}",
            *(dev_lines or []),
            "",
        ]
    lines.append("— SASTRA SoME Examination Committee")
    return "\n".join(lines)

def detect_semester(slot_dates=None):
    override = st.session_state.get("semester_override", "Auto-detect")
    if override and override != "Auto-detect":
        return override
    return SEMESTER_LABEL

def get_exam_period(slot_dates):
    if not slot_dates:
        return None, None
    sd = sorted(slot_dates)
    return sd[0], sd[-1]

def render_header(logo=True):
    if logo and os.path.exists(LOGO_FILE):
        _, c2, _ = st.columns([2, 1, 2])
        with c2:
            st.image(LOGO_FILE, width=180)
    st.markdown(
        "<h2 style='text-align:center;margin-bottom:.25rem'>"
        "SASTRA SoME End Semester Examination Duty Portal</h2>",
        unsafe_allow_html=True)
    st.markdown(
        "<h4 style='text-align:center;margin-top:0'>"
        "School of Mechanical Engineering</h4>",
        unsafe_allow_html=True)
    st.markdown(
        "<div style='text-align:center;font-weight:700;color:#1e3a5f;margin-top:-6px'>"
        f"{detect_semester()}</div>",
        unsafe_allow_html=True)
    st.markdown("---")


# ═══════════════════════════════════════════════════════════════ #
#               PARSE DUTY FILE                                  #
# ═══════════════════════════════════════════════════════════════ #
def parse_duty_file(filepath, duty_type):
    if not os.path.exists(filepath):
        return []
    try:
        raw = pd.read_excel(filepath, header=None)
    except Exception:
        return []
    try:
        pd.to_datetime(raw.iloc[0, 0])
        start = 0
    except Exception:
        start = 1
    slots = []
    for i in range(start, len(raw)):
        row = raw.iloc[i]
        d    = row.iloc[0]
        sess = row.iloc[1] if len(row) > 1 else None
        req  = row.iloc[2] if len(row) > 2 else 1
        if pd.isna(d):
            continue
        sn = normalize_session(sess)
        if sn not in ("FN", "AN"):
            continue
        try:
            date = pd.to_datetime(d).date()
        except Exception:
            continue
        try:
            required = max(int(float(req)), 0)
        except Exception:
            required = 1
        slots.append({"date": date, "session": sn, "required": required, "type": duty_type})
    return slots

@st.cache_data(ttl=300)
def load_slots(off_path, on_path):
    """Load offline duty slots from Supabase. No online duty this semester."""
    def rows_to_df(rows):
        if not rows:
            df = pd.DataFrame(columns=["Date","Session","Required"])
            df["Date"] = pd.to_datetime(df["Date"]); return df
        df = pd.DataFrame(rows)
        df.rename(columns={"duty_date":"Date","session":"Session","required":"Required"}, inplace=True)
        df["Date"]     = to_dt(df["Date"])
        df["Session"]  = df["Session"].apply(normalize_session)
        df["Required"] = pd.to_numeric(df["Required"], errors="coerce").fillna(1).astype(int)
        return df[["Date","Session","Required"]]
    _empty = pd.DataFrame(columns=["Date","Session","Required"])
    _empty["Date"] = pd.to_datetime(_empty["Date"])
    return rows_to_df(db_get_offline_slots()), _empty


# ═══════════════════════════════════════════════════════════════ #
#            WILLINGNESS FUNCTIONS (Supabase-backed)             #
# ═══════════════════════════════════════════════════════════════ #
def load_willingness():
    rows = db_get_all_willingness_rows()
    if not rows:
        return pd.DataFrame(columns=["Faculty","Date","Session","FacultyClean"])
    df = pd.DataFrame(rows)
    df.rename(columns={"faculty_name":"Faculty","duty_date":"Date","session":"Session"}, inplace=True)
    df["Faculty"] = df["Faculty"].astype(str).str.strip()
    # Supabase stores dates as YYYY-MM-DD — convert to dd-mm-yyyy so all
    # existing code that uses dayfirst=True parses them correctly
    def _reformat(v):
        s = str(v).strip()
        try:
            return pd.to_datetime(s, format="%Y-%m-%d").strftime("%d-%m-%Y")
        except Exception:
            return s
    df["Date"]         = df["Date"].apply(_reformat)
    df["Session"]      = df["Session"].astype(str).str.strip().str.upper()
    df["FacultyClean"] = df["Faculty"].apply(clean)
    return df[["Faculty","Date","Session","FacultyClean"]].reset_index(drop=True)

def get_all_willingness():
    return load_willingness()

def save_submission(faculty_name, slots):
    if st.session_state.get("_preview_fid"):
        return   # admin preview never writes
    fid = st.session_state.get("_logged_fid", faculty_name)
    db_submit_willingness(fid, faculty_name, slots)

def already_submitted(faculty_name: str) -> bool:
    fid = st.session_state.get("_preview_fid") or st.session_state.get("_logged_fid", "")
    if fid:
        return db_already_submitted(fid)
    wl = load_willingness()
    return clean(faculty_name) in wl["FacultyClean"].tolist() if not wl.empty else False


# ═══════════════════════════════════════════════════════════════ #
#        FEATURE 1 — SLOT PROBABILITY INDICATOR                  #
# ═══════════════════════════════════════════════════════════════ #
def slot_probability(all_will_df, duty_df, date_val, session_val):
    seats = 0
    if not duty_df.empty:
        m = duty_df[
            (duty_df["Date"].dt.date == date_val) &
            (duty_df["Session"].str.upper() == session_val.upper())]
        if not m.empty:
            seats = int(m["Required"].sum())

    applicants = 0
    if not all_will_df.empty and "Date" in all_will_df.columns:
        norm = to_dt(all_will_df["Date"])
        applicants = int((
            (norm.dt.date == date_val) &
            (all_will_df["Session"].str.upper() == session_val.upper())
        ).sum())

    if seats == 0:
        return {"seats": 0, "applicants": applicants,
                "probability": 0.0, "label": "No slot on this day", "colour": "#94a3b8"}
    if applicants == 0:
        return {"seats": seats, "applicants": 0,
                "probability": 100.0, "label": "High — you'd be first!", "colour": "#16a34a"}
    prob = min(seats / applicants, 1.0) * 100
    if prob >= 70:   label, colour = "High",                "#16a34a"
    elif prob >= 40: label, colour = "Medium",              "#f59e0b"
    else:            label, colour = "Low — many applicants","#dc2626"
    return {"seats": seats, "applicants": applicants,
            "probability": prob, "label": label, "colour": colour}

def render_prob_bar(info: dict, session_label: str):
    pct    = info["probability"]
    colour = info["colour"]
    st.markdown(f"""
<div style="background:#fff;border:1px solid #e2e8f0;border-radius:10px;
            padding:10px 14px;margin-bottom:8px;">
  <div style="font-weight:700;font-size:.95rem;color:#0f172a;margin-bottom:4px;">
    {session_label} &nbsp;·&nbsp;
    <span style="color:{colour}">{pct:.0f}% allocation probability</span>
  </div>
  <div style="background:#e5e7eb;border-radius:6px;height:12px;width:100%;margin:4px 0">
    <div style="background:{colour};border-radius:6px;height:12px;width:{pct:.0f}%"></div>
  </div>
  <div style="font-size:.82rem;color:#475569;margin-top:3px;">
    🎯 Seats: <b>{info['seats']}</b> &nbsp;|&nbsp;
    👥 Applied so far: <b>{info['applicants']}</b> &nbsp;|&nbsp;
    {info['label']}
  </div>
</div>""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════ #
#        DEVIATION ANALYSIS  (admin-only)                        #
# ═══════════════════════════════════════════════════════════════ #
def classify_duty(alloc_by: str, duty_date, duty_sess: str, will_set: set):
    ab = str(alloc_by).strip()
    if ab == "Willingness-Exact":
        return ("Exact Match", "✅",
                "Allotted on your exact submitted date & session", True)
    if ab == "Willingness-ACPOnline":
        return ("Session Adjusted", "🔄",
                "Your offline-date willingness was used to fill your online duty slot", True)
    if ab == "Willingness-SessionFlip":
        opp = "AN" if duty_sess == "FN" else "FN"
        return ("Session Adjusted", "🔄",
                f"You submitted {duty_date.strftime('%d-%m-%Y')} {opp} → allotted {duty_sess} "
                f"(same date, session swapped)", True)
    if ab == "Willingness-±1Day":
        closest = ""
        for direction in [1, -1]:
            adj = duty_date + datetime.timedelta(days=direction)
            for s in ["FN", "AN"]:
                if (adj, s) in will_set:
                    d = "after" if direction > 0 else "before"
                    closest = (f"You submitted {adj.strftime('%d-%m-%Y')} {s} "
                               f"→ duty shifted 1 working day {d} "
                               f"to {duty_date.strftime('%d-%m-%Y')} {duty_sess}")
                    break
            if closest: break
        return ("Date Adjusted (±1 day)", "📅",
                closest or "Allotted 1 working day from your submitted willingness", True)
    if ab == "Willingness-±2Day":
        return ("Date Adjusted (±2 days)", "📆",
                f"Allotted 2 working days from your submitted willingness "
                f"({duty_date.strftime('%d-%m-%Y')} {duty_sess})", True)
    if ab == "SAP-OnlineFallback":
        return ("SAP Online Fallback", "🔁",
                "SAP faculty assigned to online slot as fallback (P/ACP unavailable)", True)
    if ab == "Willingness-ValAdj":
        return ("Valuation-Adjacent", "🗓️",
                f"Allotted on a weekday adjacent to your valuation date "
                f"({duty_date.strftime('%d-%m-%Y')} {duty_sess})", True)
    if ab in ("Auto-Assigned", "Gap-Fill") or ab.startswith("Gap-Fill"):
        return ("Auto-Assigned", "⚙️",
                "No willingness submitted — system assigned this duty to meet slot requirements",
                False)
    return ("Not in Willingness", "🔴",
            f"No willingness found near {duty_date.strftime('%d-%m-%Y')} {duty_sess} "
            f"— system assigned to meet slot requirements", False)

def render_deviation_section(allot_rows: pd.DataFrame, will_set: set):
    if allot_rows.empty:
        st.info("No allotment data found for this faculty yet.")
        return "Not available", []

    duty_rows = []
    for _, ar in allot_rows.iterrows():
        norm = to_dt(ar["Date"])
        if pd.isna(norm): continue
        sess     = str(ar.get("Session", "")).strip().upper()
        dtype    = str(ar.get("Type", "")).strip()
        alloc_by = str(ar.get("Allocated_By", "")).strip()
        status, emoji, detail, is_matched = classify_duty(
            alloc_by, norm.date(), sess, will_set)
        duty_rows.append({
            "norm_date": norm.date(), "sess": sess, "dtype": dtype,
            "status": status, "emoji": emoji, "detail": detail,
            "is_matched": is_matched,
            "date_fmt": fmt_day(norm.strftime("%d-%m-%Y")),
        })

    total    = len(duty_rows)
    n_exact  = sum(1 for d in duty_rows if d["status"] == "Exact Match")
    n_sess   = sum(1 for d in duty_rows if d["status"] == "Session Adjusted")
    n_adj1   = sum(1 for d in duty_rows if d["status"] == "Date Adjusted (±1 day)")
    n_adj2   = sum(1 for d in duty_rows if d["status"] == "Date Adjusted (±2 days)")
    n_valadj = sum(1 for d in duty_rows if d["status"] == "Valuation-Adjacent")
    n_no     = sum(1 for d in duty_rows if not d["is_matched"])
    n_matched = n_exact + n_sess + n_adj1 + n_adj2 + n_valadj
    match_pct = n_matched / total * 100 if total else 0.0
    dev_pct   = 100.0 - match_pct
    allot_set = {(d["norm_date"], d["sess"]) for d in duty_rows}
    exact_overlap = len(will_set & allot_set)
    will_used_pct = exact_overlap / len(will_set) * 100 if will_set else 0.0

    st.markdown("---")
    st.markdown("### 📊 Willingness Match & Deviation")
    m1, m2, m3, m4 = st.columns(4)
    with m1: st.metric("Duties Allotted", total)
    with m2: st.metric("Willingness Match", f"{match_pct:.1f}%",
                       delta=f"{n_matched} of {total} within window")
    with m3: st.metric("Deviation", f"{dev_pct:.1f}%",
                       delta=f"{n_no} unmatched" if n_no else "None",
                       delta_color="inverse" if n_no else "off")
    with m4: st.metric("Your Exact Slots Used", f"{will_used_pct:.1f}%",
                       help=f"{exact_overlap} of your {len(will_set)} submitted slots allotted exactly")

    if total == 0:
        return "Not available", []
    elif dev_pct == 0.0:
        st.success("🎉 All duties were allotted exactly as per submitted willingness!")
    elif n_no == 0:
        st.info(f"ℹ️ All {total} duties fall within the willingness window. "
                f"{n_sess + n_adj1 + n_adj2} minor adjustment(s) made.")
    else:
        st.warning(f"⚠️ {n_no} of {total} duties could not be matched and were system-assigned.")

    STATUS_BG = {
        "Exact Match":              ("#d1fae5", "#065f46"),
        "Session Adjusted":         ("#fef3c7", "#92400e"),
        "Date Adjusted (±1 day)":   ("#ffedd5", "#9a3412"),
        "Date Adjusted (±2 days)":  ("#ffe4e6", "#881337"),
        "Valuation-Adjacent":       ("#ede9fe", "#5b21b6"),
        "Not in Willingness":       ("#fee2e2", "#991b1b"),
        "Auto-Assigned":            ("#e5e7eb", "#374151"),
    }
    rows_html = ""
    for d in duty_rows:
        bg, fg = STATUS_BG.get(d["status"], ("#e5e7eb", "#374151"))
        rows_html += (
            f"<tr>"
            f"<td style='padding:7px 10px;font-size:.87rem'>{d['date_fmt']}</td>"
            f"<td style='padding:7px 10px;text-align:center;font-weight:700'>{d['sess']}</td>"
            f"<td style='padding:7px 10px;text-align:center'>{d['dtype']}</td>"
            f"<td style='padding:7px 10px'><span style='display:inline-block;padding:2px 10px;"
            f"border-radius:12px;font-size:.8rem;font-weight:700;background:{bg};color:{fg}'>"
            f"{d['emoji']} {d['status']}</span></td>"
            f"<td style='padding:7px 10px;font-size:.82rem;color:#475569'>{d['detail']}</td>"
            f"</tr>")

    st.markdown(f"""
<div style="overflow-x:auto">
<table style="width:100%;border-collapse:collapse;background:#fff;
              border-radius:10px;overflow:hidden;box-shadow:0 2px 8px rgba(0,0,0,.06)">
  <thead>
    <tr style="background:#f1f5f9;font-size:.85rem;font-weight:700;color:#0f172a;">
      <th style="padding:8px 10px;text-align:left">Allotted Date</th>
      <th style="padding:8px 10px;text-align:center">Session</th>
      <th style="padding:8px 10px;text-align:center">Type</th>
      <th style="padding:8px 10px;text-align:left">Match Status</th>
      <th style="padding:8px 10px;text-align:left">Detail</th>
    </tr>
  </thead>
  <tbody>{rows_html}</tbody>
</table></div>""", unsafe_allow_html=True)

    st.markdown("#### Summary by Category")
    bd = pd.DataFrame({
        "Category": [
            "✅ Exact Match",
            "🔄 Session Adjusted (FN↔AN, same date)",
            "📅 Date Adjusted (±1 working day)",
            "📆 Date Adjusted (±2 working days)",
            "🗓️ Valuation-Adjacent (day before/after val date)",
            "🔴 Not in Willingness / Auto-Assigned",
        ],
        "Count": [n_exact, n_sess, n_adj1, n_adj2, n_valadj, n_no],
        "Share %": [f"{v/total*100:.1f}%" if total else "—"
                    for v in [n_exact, n_sess, n_adj1, n_adj2, n_valadj, n_no]],
        "Meaning": [
            "Allotted on the exact date & session you submitted",
            "Same date, but morning/afternoon slot was swapped",
            "Duty shifted by 1 working day from your submitted date",
            "Duty shifted by 2 working days from your submitted date",
            "Allotted on a weekday adjacent to your valuation date",
            "No matching date — system assigned to fill slot",
        ],
    })
    st.dataframe(bd, use_container_width=True, hide_index=True)

    dev_lines = [f"Overall match: {match_pct:.1f}%  ({n_matched}/{total} duties within window)"]
    if n_no == 0 and dev_pct == 0:
        dev_lines.append("All duties allotted exactly as per your willingness.")
    else:
        if n_exact  > 0: dev_lines.append(f"  ✅ Exact match        : {n_exact} duty(ies)")
        if n_sess   > 0: dev_lines.append(f"  🔄 Session swapped   : {n_sess} duty(ies)")
        if n_adj1   > 0: dev_lines.append(f"  📅 Date shifted ±1   : {n_adj1} duty(ies)")
        if n_adj2   > 0: dev_lines.append(f"  📆 Date shifted ±2   : {n_adj2} duty(ies)")
        if n_valadj > 0: dev_lines.append(f"  🗓️ Val-adjacent      : {n_valadj} duty(ies)")
        if n_no     > 0: dev_lines.append(f"  🔴 System-assigned   : {n_no} duty(ies)")
    match_str = f"Match {match_pct:.1f}%  ({n_matched}/{total})  |  Deviation {dev_pct:.1f}%"
    return match_str, dev_lines


# ═══════════════════════════════════════════════════════════════ #
#                    CALENDAR HEATMAP                            #
# ═══════════════════════════════════════════════════════════════ #
def render_calendar(duty_df, val_dates, title, exam_dates=None, buffer_dates=None, sat_blocked_dates=None,
                    lab_dates=None):
    st.markdown(f"#### {title}")
    if duty_df is None or duty_df.empty or "Date" not in duty_df.columns:
        st.info("Duty slots not yet published — showing the semester calendar.")
        duty_df = pd.DataFrame({"Date": pd.Series(dtype="datetime64[ns]"),
                                "Session": pd.Series(dtype=str),
                                "Required": pd.Series(dtype=int)})
    duty_df = duty_df.copy()
    duty_df["Date"] = pd.to_datetime(duty_df["Date"], errors="coerce")
    duty_df = duty_df.dropna(subset=["Date"])

    duty_df = duty_df[(duty_df["Date"].dt.date >= SEMESTER_CAL_START) &
                      (duty_df["Date"].dt.date <= SEMESTER_CAL_END)]
    # Months to show = semester window only (Nov–Dec 2026)
    months = set()
    _m = datetime.date(SEMESTER_CAL_START.year, SEMESTER_CAL_START.month, 1)
    while _m <= SEMESTER_CAL_END:
        months.add((_m.year, _m.month))
        _m = (_m.replace(day=28) + datetime.timedelta(days=4)).replace(day=1)
    months = sorted(months)

    if duty_df.empty:
        duty_map = {}
    else:
        sg = duty_df.groupby(["Date", "Session"], as_index=False)["Required"].sum()
        duty_map = {(row["Date"].date(), str(row["Session"]).upper()): int(row["Required"])
                    for _, row in sg.iterrows()}
    val_set          = set(val_dates)
    exam_set         = set(exam_dates)         if exam_dates         else set()
    buffer_set       = set(buffer_dates)       if buffer_dates       else set()
    lab_set          = set(lab_dates)          if lab_dates          else set()
    sat_blocked_set  = set(sat_blocked_dates)  if sat_blocked_dates  else set()
    WD_ORDER = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

    _exam_legend = (
        "<span style='background:#fee2e2;border:1px solid #fca5a5;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🚫 Exam Date (Locked)</span>"
    ) if exam_set else ""
    _buf_legend = (
        "<span style='background:#ffedd5;border:1px solid #fdba74;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>⛔ Buffer Day (n−1, n−2)</span>"
    ) if buffer_set else ""
    _lab_legend = (
        "<span style='background:#ede9fe;border:1px solid #c4b5fd;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🧪 Lab Exam Duty (Locked)</span>"
    ) if lab_set else ""
    _sat_blk_legend = (
        "<span style='background:#f1f5f9;border:1px solid #94a3b8;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🚷 Saturday (Not available)</span>"
    ) if sat_blocked_set else ""
    st.markdown(
        "<span style='font-size:.82rem'>"
        "<span style='background:#fce7f3;border:1px solid #f9a8d4;border-radius:4px;"
        "padding:2px 8px;margin-right:6px'>🩷 Valuation Locked</span>"
        + _sat_blk_legend + _exam_legend + _lab_legend + _buf_legend +
        "<span style='background:#fff;border:1px solid #cbd5e1;border-radius:4px;"
        "padding:2px 8px'>🔢 Number = duties required on that day/session</span>"
        "</span>", unsafe_allow_html=True)
    st.markdown("")

    for yr, mo in months:
        ms   = pd.Timestamp(year=yr, month=mo, day=1)
        me   = ms + pd.offsets.MonthEnd(0)
        days = pd.date_range(ms, me, freq="D")
        fw   = ms.weekday()
        grid = []; week = [None] * fw
        for dt in days:
            dt_date = dt.date()
            week.append(dt_date)
            if len(week) == 7:
                grid.append(week); week = []
        if week:
            week += [None] * (7 - len(week)); grid.append(week)
        grid = [w for w in grid if any(d is not None for d in w)]

        st.markdown(
            f"<div style='font-size:.95rem;font-weight:700;color:#1e3a5f;"
            f"margin:14px 0 4px 0'>{calmod.month_name[mo]} {yr}</div>",
            unsafe_allow_html=True)

        TH_DAY  = ("background:#1e3a5f;color:#fff;font-size:.8rem;font-weight:700;"
                   "text-align:center;padding:7px 4px;border:1px solid #2d4f7c;")
        TH_SESS = ("background:#dbeafe;color:#1e40af;font-size:.7rem;font-weight:700;"
                   "text-align:center;padding:4px 2px;border:1px solid #bfdbfe;width:44px;")
        TD_BASE = ("text-align:center;padding:5px 2px;border:1px solid #e2e8f0;"
                   "vertical-align:middle;min-width:44px;")

        hdr1 = "".join(f"<th colspan='2' style='{TH_DAY}'>{wd}</th>" for wd in WD_ORDER)
        hdr2 = "".join(f"<th style='{TH_SESS}'>FN</th><th style='{TH_SESS}'>AN</th>"
                       for _ in WD_ORDER)
        rows_html = ""
        for week_dates in grid:
            date_row = ""
            for dt in week_dates:
                if dt is None:
                    date_row += ("<td colspan='2' style='background:#fff;"
                                 "border:1px solid #e2e8f0;height:20px'></td>")
                else:
                    is_val    = dt in val_set
                    is_exam   = dt in exam_set
                    is_buffer = dt in buffer_set
                    is_sat_blk  = (dt in sat_blocked_set)
                    is_sun      = dt.weekday() == 6
                    if is_val:
                        bg, color = "#fce7f3", "#be185d"
                        label = f"{dt.day} 🔒"
                    elif is_exam:
                        bg, color = "#fee2e2", "#dc2626"
                        label = f"{dt.day} 🚫"
                    elif dt in lab_set:
                        bg, color = "#ede9fe", "#6d28d9"
                        label = f"{dt.day} 🧪"
                    elif is_buffer:
                        bg, color = "#ffedd5", "#c2410c"
                        label = f"{dt.day} ⛔"
                    elif is_sat_blk:
                        bg, color = "#f1f5f9", "#94a3b8"
                        label = f"{dt.day} 🚷"
                    else:
                        bg    = "#fff"
                        color = "#94a3b8" if is_sun else "#0f172a"
                        label = str(dt.day)
                    date_row += (f"<td colspan='2' style='background:{bg};"
                                 f"border:1px solid #e2e8f0;text-align:center;"
                                 f"padding:4px 2px 2px 2px;vertical-align:middle'>"
                                 f"<span style='font-size:.88rem;font-weight:800;color:{color}'>"
                                 f"{label}</span></td>")
            rows_html += f"<tr>{date_row}</tr>"

            duty_row = ""
            for dt in week_dates:
                if dt is None:
                    duty_row += ("<td style='background:#fff;border:1px solid #e2e8f0;"
                                 "min-width:44px;height:24px'></td>" * 2)
                else:
                    is_val    = dt in val_set
                    is_exam   = dt in exam_set
                    is_buffer = dt in buffer_set
                    is_sat_blk_row = (dt in sat_blocked_set)
                    for sess in ["FN", "AN"]:
                        req = duty_map.get((dt, sess), 0)
                        if is_val:
                            bg, content = "#fce7f3", ""
                        elif is_exam:
                            bg, content = "#fee2e2", ""
                        elif dt in lab_set:
                            bg, content = "#ede9fe", ""
                        elif is_buffer:
                            bg, content = "#ffedd5", ""
                        elif is_sat_blk_row:
                            bg, content = "#f1f5f9", ""
                        elif req == 0:
                            bg, content = "#fff", ""
                        else:
                            bg = "#fff"
                            content = (f"<span style='font-size:.72rem;font-style:italic;"
                                       f"font-weight:700;color:#2563eb'>{req}</span>")
                        duty_row += f"<td style='{TD_BASE}background:{bg}'>{content}</td>"
            rows_html += f"<tr>{duty_row}</tr>"

        st.markdown(f"""
<div style="overflow-x:auto;margin-bottom:20px;border-radius:10px;
            box-shadow:0 2px 12px rgba(15,23,42,.08);border:1px solid #e2e8f0">
<table style="border-collapse:collapse;width:100%;table-layout:fixed;
              font-family:Inter,sans-serif;border-radius:10px;overflow:hidden">
  <thead><tr>{hdr1}</tr><tr>{hdr2}</tr></thead>
  <tbody>{rows_html}</tbody>
</table></div>""", unsafe_allow_html=True)

    st.caption("FN = Forenoon  |  AN = Afternoon  |  Numbers = duties required on that day/session")


# ═══════════════════════════════════════════════════════════════ #
#   OPTIMIZER  — MILP (scipy HiGHS) + Smart Greedy + CP-SAT     #
# ═══════════════════════════════════════════════════════════════ #
def _load_core(log):
    if not SCIPY_OK:
        raise RuntimeError("scipy not installed. Run:  pip install scipy")

    # ── Load faculty from Supabase ────────────────────────────────
    fac_rows = db_get_all_faculty()
    if not fac_rows:
        raise RuntimeError("No faculty found in Supabase.")
    fr = pd.DataFrame(fac_rows)
    fr["Name"]        = fr["name"].astype(str).str.strip()
    fr["Designation"] = fr["designation"].astype(str).apply(_map_desig)
    # Apply per-faculty overrides
    for _i, _r in fr.iterrows():
        _fc = _norm_name(_r["Name"])
        if _fc in FACULTY_DESIG_OVERRIDE:
            fr.at[_i, "Designation"] = FACULTY_DESIG_OVERRIDE[_fc]
    fr["ID No."]      = fr["faculty_id"].astype(str).apply(_norm_id)
    fr = fr.dropna(subset=["Name"]).reset_index(drop=True)

    ALL_FAC = fr["Name"].tolist()
    FAC_IDX = {n: i for i, n in enumerate(ALL_FAC)}
    N_FAC   = len(ALL_FAC)
    fac_d   = {r["Name"]: (r["Designation"] if r["Designation"] in DESIG_RULES else "TA")
               for _, r in fr.iterrows()}
    dgroups = defaultdict(list)
    for n, d in fac_d.items():
        dgroups[d].append(n)

    # ── Valuation dates from Supabase (ISO format YYYY-MM-DD) ─────
    fac_val = {}
    for _, r in fr.iterrows():
        vd = set()
        for c in ["v1","v2","v3","v4","v5"]:
            val = r.get(c)
            if val and str(val).strip() not in ("", "None", "NaT", "nan"):
                try:
                    _v = parse_date_safe(val)
                    if pd.notna(_v):
                        vd.add(_v.date())
                except Exception:
                    pass
        fac_val[r["Name"]] = vd

    # ── Load slots from Supabase (offline only) ───────────────────
    def _rows_to_slots(rows, duty_type):
        slots = []
        for r in rows:
            try:
                dt   = parse_date_safe(r["duty_date"]).date()
                sess = normalize_session(r["session"])
                req  = max(int(r.get("required", 1)), 0)
                if sess in ("FN", "AN"):
                    slots.append({"date": dt, "session": sess,
                                  "required": req, "type": duty_type})
            except Exception:
                pass
        return slots

    s_off = _rows_to_slots(db_get_offline_slots(), "Offline")
    s_on  = []   # No online duty this semester
    ALL_S = s_off
    NS    = len(ALL_S)
    slot_dates = {s["date"] for s in ALL_S}

    wdf = get_all_willingness().drop(columns=["FacultyClean"], errors="ignore")
    if not wdf.empty:
        wdf["Date"]    = to_dt(wdf["Date"])
        wdf["Session"] = wdf["Session"].astype(str).str.strip().str.upper()
        wdf = wdf.dropna(subset=["Date"])
    submitted  = set(wdf["Faculty"].str.strip().unique()) if not wdf.empty else set()
    non_sub    = [n for n in ALL_FAC if n not in submitted]
    sub_counts = {}
    if not wdf.empty:
        for n, grp in wdf.groupby("Faculty"):
            sub_counts[n.strip()] = len(grp)

    log(f"  Faculty        : {N_FAC}")
    log(f"  Slots          : {NS}  (offline only — online duty suspended)")
    log(f"  Seats needed   : {sum(s['required'] for s in ALL_S)}")
    log(f"  Willingness    : {len(submitted)} submitted | {len(non_sub)} not submitted")

    SAT_DESIG = set(SAT_ALWAYS_DESIG)   # always Saturday-eligible (TA/RA)
    # Other designations: Saturday only where the faculty opted in via willingness
    sat_willing = defaultdict(set)
    if not wdf.empty:
        for _, _wr in wdf.iterrows():
            _wd = _wr["Date"].date()
            if _wd.weekday() == 5:
                sat_willing[str(_wr["Faculty"]).strip()].add(_wd)

    def sat_ok(fn, d2, date):
        return d2 in SAT_DESIG or date in sat_willing.get(fn, set())
    sap_faculty  = [n for n in ALL_FAC if fac_d.get(n) == "SAP"]
    sap_fallback = sap_faculty[:2]
    acp_faculty  = [n for n in ALL_FAC if fac_d.get(n) == "ACP"]
    acp_2online  = set()   # No online duty
    acp_2offline = set(acp_faculty)

    log(f"\n  ── Capacity Check ───────────────────────────────────")
    any_cap_warn = False
    for sl in ALL_S:
        avail = 0
        for fn in ALL_FAC:
            d2 = fac_d.get(fn, "TA")
            allowed = DESIG_RULES[d2][2]
            if sl["type"] not in allowed: continue
            if sl["date"] in fac_val.get(fn, set()): continue
            if sl["date"].weekday() == 5 and not sat_ok(fn, d2, sl["date"]): continue
            avail += 1
        if avail < sl["required"]:
            ds = sl["date"].strftime("%d-%m-%Y")
            log(f"  ⚠ {ds} {sl['session']} {sl['type']} — need {sl['required']} avail {avail}")
            any_cap_warn = True
    if not any_cap_warn:
        log(f"  ✓ All {NS} slots have sufficient eligible faculty")

    fexp = defaultdict(dict)
    def sset(d, k, val): d[k] = max(d.get(k, 0), val)
    def next_biz(d, steps):
        step = 1 if steps > 0 else -1
        cur = d; cnt = 0
        while cnt < abs(steps):
            cur += datetime.timedelta(days=step)
            if cur.weekday() < 5: cnt += 1
        return cur

    for _, row in wdf.iterrows():
        n = str(row.get("Faculty","")).strip()
        if n not in FAC_IDX: continue
        dt2  = row["Date"].date()
        sess = str(row["Session"]).strip().upper()
        opp  = "AN" if sess == "FN" else "FN"
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for tp in allowed:
            sset(fexp[n], (dt2, sess, tp), W_EXACT)
        for tp in allowed:
            sset(fexp[n], (dt2, opp, tp), W_FLIP)
        for direction in [+1,-1]:
            adj = next_biz(dt2, direction)
            if adj not in slot_dates: continue
            for s2 in ["FN","AN"]:
                for tp in allowed:
                    sset(fexp[n], (adj, s2, tp), W_ADJ1)
        for direction in [+2,-2]:
            adj = next_biz(dt2, direction)
            if adj not in slot_dates: continue
            for s2 in ["FN","AN"]:
                for tp in allowed:
                    sset(fexp[n], (adj, s2, tp), W_ADJ2)

    for n in ALL_FAC:
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for vd in fac_val.get(n, set()):
            for direction in [+1,-1]:
                adj = next_biz(vd, direction)
                if adj not in slot_dates: continue
                for s2 in ["FN","AN"]:
                    for tp in allowed:
                        k = (adj, s2, tp)
                        if fexp[n].get(k, 0) < W_VAL_ADJ:
                            sset(fexp[n], k, W_VAL_ADJ)

    for n in non_sub:
        allowed = DESIG_RULES[fac_d.get(n, "TA")][2]
        for s in ALL_S:
            if s["type"] in allowed:
                sset(fexp[n], (s["date"], s["session"], s["type"]), W_NON_SUB)

    def tag(fn, k, sc):
        if fn in non_sub:          return "Auto-Assigned"
        if sc >= W_EXACT:          return "Willingness-Exact"
        if sc >= W_ACP_ONLINE:     return "Willingness-ACPOnline"
        if sc >= W_FLIP:           return "Willingness-SessionFlip"
        if sc >= W_ADJ1:           return "Willingness-±1Day"
        if sc >= W_ADJ2:           return "Willingness-±2Day"
        if sc >= W_VAL_ADJ:        return "Willingness-ValAdj"
        if fn in sap_fallback:     return "SAP-OnlineFallback"
        return "OR-Assigned"

    def is_eligible(fn, sl):
        d2 = fac_d.get(fn, "TA")
        allowed = DESIG_RULES[d2][2]
        if sl["type"] not in allowed:                                        return False
        if sl["date"] in fac_val.get(fn, set()):                            return False
        # Per-faculty blackout dates (exam on that day etc.)
        if _exam_key(fn) in FACULTY_BLACKOUT_CLEAN and sl["date"] in FACULTY_BLACKOUT_CLEAN[_exam_key(fn)]:
            return False
        # Per-faculty date cap (duties must be before specified date)
        if _norm_name(fn) in FACULTY_DATE_CAP and sl["date"] >= FACULTY_DATE_CAP[_norm_name(fn)]:
            return False
        if sl["date"].weekday() == 5 and not sat_ok(fn, d2, sl["date"]):  return False
        return True

    # ── Per-faculty duty ranges ───────────────────────────────────────
    fac_duties = {fn: fac_duty_range(fn, fac_d.get(fn, "TA")) for fn in ALL_FAC}

    return dict(
        fr=fr, ALL_FAC=ALL_FAC, FAC_IDX=FAC_IDX, N_FAC=N_FAC,
        fac_d=fac_d, dgroups=dgroups, fac_val=fac_val,
        s_off=s_off, s_on=s_on, ALL_S=ALL_S, NS=NS,
        slot_dates=slot_dates, wdf=wdf,
        submitted=submitted, non_sub=non_sub, sub_counts=sub_counts,
        fexp=fexp, tag=tag, is_eligible=is_eligible,
        sap_fallback=sap_fallback, SAT_DESIG=SAT_DESIG,
        acp_2online=acp_2online, acp_2offline=acp_2offline,
        fac_duties=fac_duties,
    )


def _build_summary(assigned, core):
    ALL_FAC = core["ALL_FAC"]; fac_d = core["fac_d"]
    ALL_S   = core["ALL_S"];   submitted = core["submitted"]
    sub_counts = core["sub_counts"]
    alloc = pd.DataFrame(assigned)
    alloc["Date"] = pd.to_datetime(alloc["Date"]).dt.strftime("%d-%m-%Y")
    alloc = alloc.sort_values(["Date","Session","Name"]).reset_index(drop=True)
    alloc.insert(0, "Sl.No", alloc.index + 1)

    sumrows = []
    fac_duties_bs = core.get("fac_duties", {})
    for fn in ALL_FAC:
        d2 = fac_d[fn]; dr = DESIG_RULES[d2]
        min_d, _ = fac_duties_bs.get(fn, (dr[0], dr[1]))
        rf = alloc[alloc["Name"] == fn]; ab = rf["Allocated_By"]
        tot = len(rf); wt = int(ab.isin(WILL_TAGS).sum())
        sumrows.append({
            "Name": fn, "Designation": d2,
            "Submitted":        "Yes" if fn in submitted else "No",
            "Submitted_Count":  sub_counts.get(fn, 0),
            "Required_Duties":  min_d, "Assigned_Duties": tot,
            "Willingness_Total":wt,
            "Match_%":          f"{wt/tot*100:.0f}%" if tot else "N/A",
            "Exact_Match":      int((ab=="Willingness-Exact").sum()),
            "ACP_Online":       int((ab=="Willingness-ACPOnline").sum()),
            "Session_Flip":     int((ab=="Willingness-SessionFlip").sum()),
            "Adj_±1Day":        int((ab=="Willingness-±1Day").sum()),
            "Adj_±2Day":        int((ab=="Willingness-±2Day").sum()),
            "Val_Adj":          int((ab=="Willingness-ValAdj").sum()),
            "SAP_Online":       int((ab=="SAP-OnlineFallback").sum()),
            "Auto_Assigned":    int(ab.isin(["Auto-Assigned","OR-Assigned","Gap-Fill"]).sum()),
            "Online":  int((rf["Type"]=="Online").sum()),
            "Offline": int((rf["Type"]=="Offline").sum()),
            "Gap":     max(min_d-tot, 0),
        })
    sumdf = pd.DataFrame(sumrows)

    slotrows = []
    for sl in ALL_S:
        ds = pd.Timestamp(sl["date"]).strftime("%d-%m-%Y")
        na = len(alloc[(alloc["Date"]==ds)&(alloc["Session"]==sl["session"])&(alloc["Type"]==sl["type"])])
        slotrows.append({
            "Date": ds, "Session": sl["session"], "Type": sl["type"],
            "Required": sl["required"], "Assigned": na,
            "Status": "✓" if na >= sl["required"] else f"✗ short {sl['required']-na}"
        })
    slotdf = pd.DataFrame(slotrows)

    desigrows = []
    for d2 in DESIG_RULES:
        sub2 = sumdf[sumdf["Designation"]==d2]
        if sub2.empty: continue
        dr = DESIG_RULES[d2]
        on = int(sub2["Online"].sum()); of = int(sub2["Offline"].sum())
        desigrows.append({
            "Designation": d2, "Faculty_Count": len(sub2),
            "Duties_Per_Person": dr[0], "Total_Required": dr[0]*len(sub2),
            "Total_Assigned": on+of,
            "Willingness_Matched": int(sub2["Willingness_Total"].sum()),
            "Auto_Assigned": int(sub2["Auto_Assigned"].sum()),
            "Online": on, "Offline": of,
        })
    desigdf = pd.DataFrame(desigrows)
    return alloc, sumdf, slotdf, desigdf


def _greedy_solve(core, log):
    ALL_FAC = core["ALL_FAC"]; fac_d = core["fac_d"]
    ALL_S   = core["ALL_S"];   fexp  = core["fexp"]
    tag     = core["tag"];     is_eligible = core["is_eligible"]
    non_sub = core["non_sub"]; SAT_DESIG = core["SAT_DESIG"]
    sap_fallback = core["sap_fallback"]
    acp_2online  = core["acp_2online"]
    acp_2offline = core["acp_2offline"]

    alloc_count  = defaultdict(int)
    used_dt_sess = defaultdict(set)
    acp_online   = defaultdict(int)
    acp_offline  = defaultdict(int)

    # Shuffle faculty order with fixed seed — removes alphabetical tie-breaking bias
    # while keeping results reproducible across runs
    import random as _random
    _rng = _random.Random(42)
    ALL_FAC_SHUFFLED = ALL_FAC[:]
    _rng.shuffle(ALL_FAC_SHUFFLED)

    def rem(fn):
        _, max_d = fac_duty_range(fn, fac_d.get(fn, "TA"))
        return max_d - alloc_count[fn]

    def eligible(fn, sl):
        if not is_eligible(fn, sl):        return False
        if rem(fn) <= 0:                   return False
        if (sl["date"], sl["session"]) in used_dt_sess[fn]: return False
        d2 = fac_d[fn]
        if d2 == "ACP":
            if sl["type"] == "Offline":
                limit_off = 2
                if acp_offline[fn] >= limit_off: return False
        return True

    def score(fn, sl):
        k  = (sl["date"], sl["session"], sl["type"])
        sc = fexp[fn].get(k, 0)
        min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
        # Equity: prioritise faculty with fewer duties filled relative to their target
        filled_ratio = alloc_count[fn] / min_d if min_d > 0 else 1.0
        return (sc, -filled_ratio)

    assigned = []

    # ── Forced assignments — specific faculty on specific dates ────────────────
    _sat_slots_sorted = sorted(
        [s for s in ALL_S if s["date"].weekday() == 5],
        key=lambda s: (s["date"], s["session"]))

    def _force_assign(fn, fslot):
        """Add a forced assignment if slot exists and faculty not already on that date/sess."""
        if (fslot["date"], fslot["session"]) in used_dt_sess[fn]:
            return False
        for _sl in ALL_S:
            if _sl["date"] == fslot["date"] and _sl["session"] == fslot["session"]:
                k  = (fslot["date"], fslot["session"], "Offline")
                sc = fexp[fn].get(k, 0)
                assigned.append({"Name": fn, "Date": fslot["date"],
                                 "Session": fslot["session"], "Type": "Offline",
                                 "Allocated_By": tag(fn, k, sc)})
                alloc_count[fn] += 1
                used_dt_sess[fn].add((fslot["date"], fslot["session"]))
                return True
        return False  # slot not in exam schedule

    # Apply FORCED_ASSIGNMENTS (if any)
    for _fn in ALL_FAC:
        _fnc = _norm_name(_fn)
        if _fnc in FORCED_ASSIGNMENTS:
            for _fslot in FORCED_ASSIGNMENTS[_fnc]:
                if is_eligible(_fn, _fslot):
                    _force_assign(_fn, _fslot)

    # Antony gets 2 Saturday duties (covers the 20th Saturday slot)
    _antony_fn = next((fn for fn in ALL_FAC if _norm_name(fn) == ANTONY_NORM_NAME), None)
    if _antony_fn:
        _antony_sat_count = 0
        for _sat_sl in _sat_slots_sorted:
            if _antony_sat_count >= 2:
                break
            if not is_eligible(_antony_fn, _sat_sl):
                continue
            if (_sat_sl["date"], _sat_sl["session"]) in used_dt_sess[_antony_fn]:
                continue
            if _force_assign(_antony_fn, _sat_sl):
                _antony_sat_count += 1

    for sl in sorted(ALL_S, key=lambda s: -s["required"]):
        needed = sl["required"]
        cands  = sorted([fn for fn in ALL_FAC_SHUFFLED if eligible(fn, sl)],
                        key=lambda fn: score(fn, sl), reverse=True)
        for fn in cands[:needed]:
            k  = (sl["date"], sl["session"], sl["type"])
            sc = fexp[fn].get(k, 0)
            assigned.append({"Name": fn, "Date": sl["date"],
                             "Session": sl["session"], "Type": sl["type"],
                             "Allocated_By": tag(fn, k, sc)})
            alloc_count[fn] += 1
            used_dt_sess[fn].add((sl["date"], sl["session"]))
            if fac_d[fn] == "ACP":
                if sl["type"] == "Offline": acp_offline[fn] += 1

        filled = sum(1 for a in assigned
                     if a["Date"]==sl["date"] and a["Session"]==sl["session"] and a["Type"]==sl["type"])
        if filled < needed:
            extras = sorted(
                [fn for fn in ALL_FAC_SHUFFLED
                 if is_eligible(fn, sl) and (sl["date"],sl["session"]) not in used_dt_sess[fn]
                 and fn not in [a["Name"] for a in assigned
                                if a["Date"]==sl["date"] and a["Session"]==sl["session"] and a["Type"]==sl["type"]]],
                key=lambda fn: score(fn, sl), reverse=True)
            for fn in extras[:needed-filled]:
                k  = (sl["date"], sl["session"], sl["type"])
                sc = fexp[fn].get(k, 0)
                assigned.append({"Name": fn, "Date": sl["date"],
                                 "Session": sl["session"], "Type": sl["type"],
                                 "Allocated_By": tag(fn, k, sc)})
                alloc_count[fn] += 1
                used_dt_sess[fn].add((sl["date"], sl["session"]))

    for fn in ALL_FAC_SHUFFLED:
        min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
        needed = min_d - alloc_count[fn]
        if needed <= 0: continue
        for sl in sorted(ALL_S, key=lambda s: fexp[fn].get(
                (s["date"],s["session"],s["type"]),0), reverse=True):
            if needed <= 0: break
            if not is_eligible(fn, sl): continue
            if (sl["date"],sl["session"]) in used_dt_sess[fn]: continue
            k  = (sl["date"], sl["session"], sl["type"])
            sc = fexp[fn].get(k, 0)
            assigned.append({"Name": fn, "Date": sl["date"],
                             "Session": sl["session"], "Type": sl["type"],
                             "Allocated_By": tag(fn, k, sc)})
            alloc_count[fn] += 1
            used_dt_sess[fn].add((sl["date"],sl["session"]))
            needed -= 1

    return assigned


def _cpsat_solve(core, log):
    if not ORTOOLS_OK:
        log("  CP-SAT not available.")
        return None

    ALL_FAC = core["ALL_FAC"]; FAC_IDX = core["FAC_IDX"]
    N_FAC   = core["N_FAC"];   fac_d   = core["fac_d"]
    ALL_S   = core["ALL_S"];   NS      = core["NS"]
    fexp    = core["fexp"];    tag     = core["tag"]
    submitted  = core["submitted"]; non_sub = core["non_sub"]
    is_eligible = core["is_eligible"]
    dt_sess = defaultdict(list)
    for si, sl in enumerate(ALL_S):
        dt_sess[(sl["date"], sl["session"])].append(si)

    SLACK_PENALTY = 10_000_000
    GAP_PENALTY   =    500_000

    try:
        mdl = cp_model.CpModel()
        x = {}
        for fi, fn in enumerate(ALL_FAC):
            for si, sl in enumerate(ALL_S):
                x[(fi, si)] = mdl.NewBoolVar(f"x_{fi}_{si}")
                if not is_eligible(fn, sl):
                    mdl.Add(x[(fi, si)] == 0)

        sv = {}
        for si, sl in enumerate(ALL_S):
            sv[si] = mdl.NewIntVar(0, sl["required"], f"sv_{si}")

        gv = {}
        for fi, fn in enumerate(ALL_FAC):
            min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
            gv[fi] = mdl.NewIntVar(0, min_d, f"gv_{fi}")

        obj_terms = []
        for fi, fn in enumerate(ALL_FAC):
            for si, sl in enumerate(ALL_S):
                if not is_eligible(fn, sl): continue
                k  = (sl["date"], sl["session"], sl["type"])
                sc = fexp[fn].get(k, 0)
                min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
                # Equity cap: scale score by 1/min_duties so no faculty dominates
                equity_sc = int(sc / max(min_d, 1))
                if sc > 0:
                    obj_terms.append(equity_sc * x[(fi, si)])
                elif fn in submitted:
                    obj_terms.append(-PENALTY * x[(fi, si)])
        for si in range(NS):
            obj_terms.append(-SLACK_PENALTY * sv[si])
        for fi in range(N_FAC):
            obj_terms.append(-GAP_PENALTY * gv[fi])
        mdl.Maximize(sum(obj_terms))

        for si, sl in enumerate(ALL_S):
            mdl.Add(sum(x[(f, si)] for f in range(N_FAC)) + sv[si] == sl["required"])
        for fi, fn in enumerate(ALL_FAC):
            min_d, max_d = fac_duty_range(fn, fac_d.get(fn, "TA"))
            mdl.Add(sum(x[(fi, s)] for s in range(NS)) <= max_d)
            mdl.Add(sum(x[(fi, s)] for s in range(NS)) + gv[fi] == min_d)
        for fi in range(N_FAC):
            for sil in dt_sess.values():
                if len(sil) > 1:
                    mdl.Add(sum(x[(fi, si)] for si in sil) <= 1)

        acp_2offline = core["acp_2offline"]
        off_i = [i for i, s in enumerate(ALL_S) if s["type"] == "Offline"]
        for fn in ALL_FAC:
            if fac_d[fn] != "ACP": continue
            fi = FAC_IDX[fn]
            if off_i: mdl.Add(sum(x[(fi, si)] for si in off_i) <= 2)

        # Forced assignments (named date/session pairs)
        for _fn in ALL_FAC:
            _fnc = _norm_name(_fn)
            _fi  = FAC_IDX.get(_fn)
            if _fi is None: continue

            if _fnc in FORCED_ASSIGNMENTS:
                for _fslot in FORCED_ASSIGNMENTS[_fnc]:
                    _si = next((i for i, s in enumerate(ALL_S)
                                if s["date"] == _fslot["date"] and s["session"] == _fslot["session"]), None)
                    if _si is not None and is_eligible(_fn, ALL_S[_si]):
                        mdl.Add(x[(_fi, _si)] == 1)

            # Antony: force 2 Saturday slots
            if _fnc == ANTONY_NORM_NAME:
                _sat_sis = [i for i, s in enumerate(ALL_S)
                            if s["date"].weekday() == 5 and is_eligible(_fn, s)]
                for _si in _sat_sis[:2]:
                    mdl.Add(x[(_fi, _si)] == 1)



        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds  = 300
        solver.parameters.num_search_workers   = 4
        solver.parameters.log_search_progress  = False

        status = solver.Solve(mdl)
        log(f"  CP-SAT status : {solver.StatusName(status)}")
        log(f"  Wall time     : {solver.WallTime():.1f}s")

        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            log("  ⚠ CP-SAT could not find a solution — skipping Method C")
            return None

        assigned = []
        for fi, fn in enumerate(ALL_FAC):
            for si, sl in enumerate(ALL_S):
                if solver.Value(x[(fi, si)]) == 1:
                    k  = (sl["date"], sl["session"], sl["type"])
                    sc = fexp[fn].get(k, 0)
                    assigned.append({"Name": fn, "Date": sl["date"],
                                     "Session": sl["session"], "Type": sl["type"],
                                     "Allocated_By": tag(fn, k, sc)})

        slack_total = sum(solver.Value(sv[si]) for si in range(NS))
        gap_total   = sum(solver.Value(gv[fi]) for fi in range(N_FAC))
        if slack_total > 0:
            log(f"  ⚠ Unfilled seats : {slack_total}")
            for si, sl in enumerate(ALL_S):
                sk = solver.Value(sv[si])
                if sk > 0:
                    log(f"    {sl['date'].strftime('%d-%m-%Y')} {sl['session']} {sl['type']} short {sk}")
        else:
            log("  ✓ All slots fully filled")
        if gap_total > 0:
            log(f"  ⚠ Faculty gaps   : {gap_total}")
        else:
            log("  ✓ All faculty assigned correct duty count")
        return assigned

    except Exception as e:
        log(f"  ✗ CP-SAT error: {e}")
        return None


def _milp_solve(core, log):
    ALL_FAC = core["ALL_FAC"]; FAC_IDX = core["FAC_IDX"]
    N_FAC   = core["N_FAC"];   fac_d   = core["fac_d"]
    ALL_S   = core["ALL_S"];   NS      = core["NS"]
    fexp    = core["fexp"];    tag     = core["tag"]
    submitted = core["submitted"]; non_sub = core["non_sub"]
    is_eligible = core["is_eligible"]
    sap_fallback = core["sap_fallback"]

    SLACK_PENALTY = 10_000_000
    GAP_PENALTY   =    500_000

    def v(fi, si): return fi * NS + si
    def sv(si):    return N_FAC * NS + si
    def gv(fi):    return N_FAC * NS + NS + fi

    NV    = N_FAC * NS + NS + N_FAC
    c_obj = np.zeros(NV)
    lb    = np.zeros(NV)
    ub    = np.ones(NV)

    for fi, fn in enumerate(ALL_FAC):
        for si, sl in enumerate(ALL_S):
            if not is_eligible(fn, sl):
                ub[v(fi, si)] = 0.0; continue
            k  = (sl["date"], sl["session"], sl["type"])
            sc = fexp[fn].get(k, 0)
            min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
            equity_sc = sc / max(min_d, 1)  # scale so faculty with more duties don't dominate
            if equity_sc > 0:
                c_obj[v(fi, si)] = -float(equity_sc)
            elif fn in submitted:
                c_obj[v(fi, si)] = float(PENALTY)

    for si, sl in enumerate(ALL_S):
        ub[sv(si)]    = float(sl["required"])
        c_obj[sv(si)] = float(SLACK_PENALTY)

    for fi, fn in enumerate(ALL_FAC):
        min_d, _ = fac_duty_range(fn, fac_d.get(fn, "TA"))
        ub[gv(fi)]    = float(min_d)
        c_obj[gv(fi)] = float(GAP_PENALTY)

    rA, cA, dA, blo, bhi = [], [], [], [], []
    nc = [0]
    def add_con(vids, coeffs, lo, hi):
        for vi, co in zip(vids, coeffs):
            rA.append(nc[0]); cA.append(vi); dA.append(float(co))
        blo.append(float(lo)); bhi.append(float(hi)); nc[0] += 1

    for si, sl in enumerate(ALL_S):
        add_con([v(f,si) for f in range(N_FAC)] + [sv(si)],
                [1]*N_FAC + [1], sl["required"], sl["required"])

    for fi, fn in enumerate(ALL_FAC):
        min_d, max_d = fac_duty_range(fn, fac_d.get(fn, "TA"))
        add_con([v(fi,s) for s in range(NS)], [1]*NS, 0, max_d)
        add_con([v(fi,s) for s in range(NS)] + [gv(fi)],
                [1]*NS + [1], min_d, min_d)

    dt_sess = defaultdict(list)
    for si, sl in enumerate(ALL_S):
        dt_sess[(sl["date"], sl["session"])].append(si)
    for fi in range(N_FAC):
        for sil in dt_sess.values():
            if len(sil) > 1:
                add_con([v(fi,si) for si in sil], [1]*len(sil), 0, 1)

    acp_2offline = core["acp_2offline"]
    off_i = [i for i, s in enumerate(ALL_S) if s["type"] == "Offline"]
    for fn in ALL_FAC:
        if fac_d[fn] != "ACP": continue
        fi = FAC_IDX[fn]
        if off_i:
            add_con([v(fi,si) for si in off_i], [1]*len(off_i), 0, 2)

    # Forced assignments — set lower bound = 1 for forced (faculty, slot) pairs
    for _fn in ALL_FAC:
        _fnc = _norm_name(_fn)
        _fi  = FAC_IDX.get(_fn)
        if _fi is None: continue

        # Named forced date assignments
        if _fnc in FORCED_ASSIGNMENTS:
            for _fslot in FORCED_ASSIGNMENTS[_fnc]:
                _si = next((i for i, s in enumerate(ALL_S)
                            if s["date"] == _fslot["date"] and s["session"] == _fslot["session"]), None)
                if _si is not None and is_eligible(_fn, ALL_S[_si]):
                    lb[v(_fi, _si)] = 1.0

        # Antony: force 2 Saturday slots
        if _fnc == ANTONY_NORM_NAME:
            _sat_count = 0
            for _si, _sl in enumerate(ALL_S):
                if _sat_count >= 2: break
                if _sl["date"].weekday() == 5 and is_eligible(_fn, _sl):
                    lb[v(_fi, _si)] = 1.0
                    _sat_count += 1

    from scipy.sparse import csc_matrix
    A = csc_matrix((dA, (rA, cA)), shape=(nc[0], NV))
    log(f"  Variables    : {NV}  Constraints: {nc[0]}")

    res = milp(
        c=c_obj,
        constraints=LinearConstraint(A, blo, bhi),
        integrality=np.ones(NV),
        bounds=Bounds(lb=lb, ub=ub),
        options={"disp": False, "time_limit": 300}
    )
    log(f"  HiGHS status : {res.message}")

    if res.status not in (0, 1):
        log("  ⚠ MILP failed — using greedy fallback")
        return _greedy_solve(core, log)

    xh = np.round(res.x).astype(int)
    assigned = []
    for fi, fn in enumerate(ALL_FAC):
        for si, sl in enumerate(ALL_S):
            if xh[v(fi, si)] == 1:
                k  = (sl["date"], sl["session"], sl["type"])
                sc = fexp[fn].get(k, 0)
                assigned.append({"Name": fn, "Date": sl["date"],
                                 "Session": sl["session"], "Type": sl["type"],
                                 "Allocated_By": tag(fn, k, sc)})

    slack_slots = [(si, sl) for si, sl in enumerate(ALL_S) if xh[sv(si)] > 0]
    gap_fac     = [(fi, fn) for fi, fn in enumerate(ALL_FAC) if xh[gv(fi)] > 0]
    if slack_slots:
        log(f"  ⚠ Unfilled seats: {sum(xh[sv(si)] for si,_ in slack_slots)}")
        for si, sl in slack_slots:
            log(f"    {sl['date'].strftime('%d-%m-%Y')} {sl['session']} {sl['type']} short {xh[sv(si)]}")
    else:
        log("  ✓ All slots fully filled")
    if gap_fac:
        log(f"  ⚠ Faculty duty gaps: {sum(xh[gv(fi)] for fi,_ in gap_fac)}")
        for fi, fn in gap_fac:
            log(f"    {fn} — short {xh[gv(fi)]}")
    else:
        log("  ✓ All faculty assigned correct duty count")

    return assigned


def _log_result(assigned, core, method, log):
    ALL_FAC   = core["ALL_FAC"]; fac_d    = core["fac_d"]
    submitted = core["submitted"]; non_sub = core["non_sub"]
    ALL_S     = core["ALL_S"];   sub_counts = core["sub_counts"]
    sap_fallback = core["sap_fallback"]

    alloc, sumdf, slotdf, desigdf = _build_summary(assigned, core)
    tot = len(alloc); ab2 = alloc["Allocated_By"]
    unmet = slotdf[~slotdf["Status"].str.startswith("✓")]
    gaps  = sumdf[sumdf["Gap"] > 0]
    sub_alloc = alloc[alloc["Name"].isin(submitted)]
    will_matched = int(sub_alloc["Allocated_By"].isin(WILL_TAGS).sum()) if not sub_alloc.empty else 0
    will_total   = len(sub_alloc)
    overall_pct  = will_matched / will_total * 100 if will_total > 0 else 0

    log(f"\n  {'='*54}")
    log(f"  RESULT  [{method}]")
    log(f"  {'='*54}")
    log(f"  Total assignments   : {tot}")
    log(f"  ├─ Exact            : {int((ab2=='Willingness-Exact').sum())}")
    log(f"  ├─ Session flip     : {int((ab2=='Willingness-SessionFlip').sum())}")
    log(f"  ├─ ±1 day           : {int((ab2=='Willingness-±1Day').sum())}")
    log(f"  ├─ ±2 days          : {int((ab2=='Willingness-±2Day').sum())}")
    log(f"  ├─ Val-adjacent     : {int((ab2=='Willingness-ValAdj').sum())}")
    log(f"  └─ Auto/OR-assigned : {int(ab2.isin(['Auto-Assigned','OR-Assigned','Gap-Fill']).sum())}")
    log(f"\n  ★ Willingness match : {overall_pct:.1f}%  ({will_matched}/{will_total})")
    log(f"  Slots filled        : {len(slotdf)-len(unmet)}/{len(slotdf)}"
        + (" ✓" if len(unmet)==0 else f"  ⚠ {len(unmet)} unmet"))
    log(f"  Faculty targets     : {len(sumdf)-len(gaps)}/{len(sumdf)}"
        + (" ✓" if len(gaps)==0 else f"  ⚠ {len(gaps)} short"))

    acp = sumdf[sumdf["Designation"]=="ACP"]
    p   = sumdf[sumdf["Designation"]=="P"]
    log(f"  P   (1 offline)     : {len(p[p['Offline']>=1])}/{len(p)}")
    log(f"  ACP summary (all offline this semester):")
    for _, r in acp.iterrows():
        off_c = int(r["Offline"])
        log(f"    {r['Name']:<32} {off_c} offline")

    return alloc, sumdf, slotdf, desigdf, overall_pct, len(unmet), len(gaps)


def run_optimizer(log_box):
    log_lines = []
    def log(m=""):
        log_lines.append(m)
        log_box.code("\n".join(log_lines), language="text")

    log("=" * 62)
    log("  SASTRA SoME Duty Optimizer  v4")
    log(f"  Method A: scipy HiGHS MILP")
    log(f"  Method B: Smart Greedy")
    log(f"  Method C: OR-Tools CP-SAT  ({'✅ Available' if ORTOOLS_OK else '❌ Not available'})")
    log(f"  NOTE: Online duty suspended — all slots are Offline this semester")
    log("=" * 62)

    log("\n  Loading data...")
    core = _load_core(log)
    results = {}

    log("\n" + "─"*62)
    log("  METHOD A — scipy HiGHS MILP")
    log("─"*62)
    try:
        assigned_A = _milp_solve(core, log)
        alloc_A, sumdf_A, slotdf_A, desigdf_A, pct_A, unmet_A, gaps_A = \
            _log_result(assigned_A, core, "MILP", log)
        results["MILP"] = dict(alloc=alloc_A, sumdf=sumdf_A, slotdf=slotdf_A,
                               desigdf=desigdf_A, pct=pct_A, unmet=unmet_A, gaps=gaps_A)
    except Exception as e:
        log(f"  ✗ MILP error: {e} — using greedy fallback")
        assigned_A = _greedy_solve(core, log)
        alloc_A, sumdf_A, slotdf_A, desigdf_A, pct_A, unmet_A, gaps_A = \
            _log_result(assigned_A, core, "MILP→Greedy", log)
        results["MILP"] = dict(alloc=alloc_A, sumdf=sumdf_A, slotdf=slotdf_A,
                               desigdf=desigdf_A, pct=pct_A, unmet=unmet_A, gaps=gaps_A)

    log("\n" + "─"*62)
    log("  METHOD B — Smart Greedy")
    log("─"*62)
    try:
        assigned_B = _greedy_solve(core, log)
        alloc_B, sumdf_B, slotdf_B, desigdf_B, pct_B, unmet_B, gaps_B = \
            _log_result(assigned_B, core, "Greedy", log)
        results["Greedy"] = dict(alloc=alloc_B, sumdf=sumdf_B, slotdf=slotdf_B,
                                 desigdf=desigdf_B, pct=pct_B, unmet=unmet_B, gaps=gaps_B)
    except Exception as e:
        log(f"  ✗ Greedy error: {e}")
        results["Greedy"] = results["MILP"]
        pct_B, unmet_B, gaps_B = pct_A, unmet_A, gaps_A
        alloc_B, sumdf_B, slotdf_B = alloc_A, sumdf_A, slotdf_A

    pct_C = unmet_C = gaps_C = None
    alloc_C = sumdf_C = slotdf_C = desigdf_C = None
    if ORTOOLS_OK:
        log("\n" + "─"*62)
        log("  METHOD C — OR-Tools CP-SAT")
        log("─"*62)
        try:
            assigned_C = _cpsat_solve(core, log)
            if assigned_C is not None:
                alloc_C, sumdf_C, slotdf_C, desigdf_C, pct_C, unmet_C, gaps_C = \
                    _log_result(assigned_C, core, "CP-SAT", log)
                results["CP-SAT"] = dict(alloc=alloc_C, sumdf=sumdf_C, slotdf=slotdf_C,
                                         desigdf=desigdf_C, pct=pct_C, unmet=unmet_C, gaps=gaps_C)
        except Exception as e:
            log(f"  ✗ CP-SAT error: {e}")
    else:
        log("\n  METHOD C — OR-Tools CP-SAT  ❌ Skipped (not installed)")

    log("\n" + "═"*62)
    log("  COMPARISON SUMMARY")
    log("═"*62)
    hdr = f"  {'Metric':<30} {'MILP':>10} {'Greedy':>10}"
    if pct_C is not None: hdr += f" {'CP-SAT':>10}"
    log(hdr); log("  " + "─"*58)
    def _row(label, vA, vB, vC, fmt="{}"):
        fA = fmt.format(vA) if vA is not None else "—"
        fB = fmt.format(vB) if vB is not None else "—"
        line = f"  {label:<30} {fA:>10} {fB:>10}"
        if pct_C is not None: line += f" {(fmt.format(vC) if vC is not None else '—'):>10}"
        log(line)
    _row("Willingness match %", pct_A, pct_B, pct_C, fmt="{:.1f}%")
    _row("Unmet slots",         unmet_A, unmet_B, unmet_C)
    _row("Faculty duty gaps",   gaps_A,  gaps_B,  gaps_C)
    _row("Total assignments",   len(alloc_A), len(alloc_B),
         len(alloc_C) if alloc_C is not None else None)
    log("  " + "─"*58)

    candidates = [("MILP", pct_A, unmet_A, gaps_A), ("Greedy", pct_B, unmet_B, gaps_B)]
    if pct_C is not None: candidates.append(("CP-SAT", pct_C, unmet_C, gaps_C))
    candidates.sort(key=lambda x: (x[2], x[3], -x[1]))
    rec = candidates[0][0]
    method_letter = {"MILP":"A","Greedy":"B","CP-SAT":"C"}[rec]
    log(f"  ★ Recommendation : METHOD {method_letter} ({rec})")

    alloc_A.to_excel("Final_Allocation_MILP.xlsx",   index=False)
    alloc_B.to_excel("Final_Allocation_Greedy.xlsx", index=False)
    if alloc_C is not None:
        alloc_C.to_excel("Final_Allocation_CPSAT.xlsx", index=False)

    best = results[rec]
    best["alloc"].to_excel(FINAL_ALLOC_FILE, index=False)
    with pd.ExcelWriter(ALLOC_REPORT_FILE, engine="openpyxl") as writer:
        best["alloc"].to_excel(writer,   sheet_name="Full_Allocation",   index=False)
        best["sumdf"].to_excel(writer,   sheet_name="Faculty_Summary",   index=False)
        best["slotdf"].to_excel(writer,  sheet_name="Slot_Verification", index=False)
        alloc_A.to_excel(writer, sheet_name="MILP_Allocation",   index=False)
        alloc_B.to_excel(writer, sheet_name="Greedy_Allocation", index=False)
        if alloc_C is not None:
            alloc_C.to_excel(writer, sheet_name="CPSAT_Allocation", index=False)

    st.session_state.update({
        "alloc_milp":    alloc_A,   "alloc_greedy":  alloc_B,   "alloc_cpsat":   alloc_C,
        "sumdf_milp":    sumdf_A,   "sumdf_greedy":  sumdf_B,   "sumdf_cpsat":   sumdf_C,
        "slotdf_milp":   slotdf_A,  "slotdf_greedy": slotdf_B,  "slotdf_cpsat":  slotdf_C,
        "pct_milp":      pct_A,     "pct_greedy":    pct_B,     "pct_cpsat":     pct_C,
        "unmet_milp":    unmet_A,   "unmet_greedy":  unmet_B,   "unmet_cpsat":   unmet_C,
        "gaps_milp":     gaps_A,    "gaps_greedy":   gaps_B,    "gaps_cpsat":    gaps_C,
        "recommended":   rec,       "cpsat_ok":      ORTOOLS_OK,
    })
    log(f"\n  Saved: {FINAL_ALLOC_FILE}  ({rec} — default)")
    return best["alloc"], best["sumdf"], best["slotdf"], best.get("desigdf", pd.DataFrame())


# ═══════════════════════════════════════════════════════════════ #
#              SESSION STATE DEFAULTS                            #
# ═══════════════════════════════════════════════════════════════ #
_defaults = {
    "logged_in":           False,
    "faculty_id":          "",
    "faculty_name":        "",
    "faculty_clean":       "",
    "is_admin":            False,
    "must_change_pw":      False,
    "panel_mode":          "User View",
    "user_panel_mode":     "Willingness",
    "selected_faculty":    "",
    "selected_slots":      [],
    "confirm_delete":          False,
    "confirm_delete_will":     False,
    "confirm_delete_allot":    False,
    "confirm_full_reset":      False,
    "pending_submissions": pd.DataFrame(columns=["Faculty", "Date", "Session"]),
}
for k, val in _defaults.items():
    if k not in st.session_state:
        st.session_state[k] = val


# ═══════════════════════════════════════════════════════════════ #
#                      LOGIN PAGE                                #
# ═══════════════════════════════════════════════════════════════ #
def page_login(fac_df):
    render_header(logo=True)
    _, c2, _ = st.columns([1, 2, 1])
    with c2:
        st.markdown(
            '<div class="card"><div class="card-title">🔒 Faculty Login</div>'
            '<p class="card-sub">Enter your Faculty ID and password to continue.</p></div>',
            unsafe_allow_html=True)

        if not BCRYPT_OK:
            st.warning("⚠ bcrypt not installed — run `pip install bcrypt` for full security.")

        fid_input = st.text_input("Faculty ID", placeholder="e.g. C870 or RS602").strip().upper().replace(" ", "")
        pwd = st.text_input("Password", type="password")

        if st.button("Sign In", use_container_width=True):
            if not fid_input or not pwd:
                st.error("Please enter both your Faculty ID and password.")
            else:
                db_row = db_get_faculty_by_id(fid_input)
                if not db_row:
                    st.error(
                        f"Faculty ID **{fid_input}** not found. "
                        "Enter your ID exactly as on your ID card (e.g. C2086, RS1051). "
                        "Contact admin if this persists.")
                elif verify_password(pwd, db_row["password_hash"]):
                    st.session_state.logged_in      = True
                    st.session_state.faculty_id     = fid_input
                    st.session_state._logged_fid    = fid_input
                    st.session_state.faculty_name   = str(db_row["name"]).strip()
                    st.session_state.faculty_clean  = clean(db_row["name"])
                    st.session_state.is_admin       = db_row.get("is_admin", False)
                    st.session_state.must_change_pw = db_row.get("must_change_pw", False)
                    st.rerun()
                else:
                    st.error(f"Incorrect password. Default first-time password is: **{DEFAULT_PASSWORD}**")

        st.markdown(
            f'<div class="blink" style="text-align:center;font-size:.96rem;margin-top:10px">'
            f'🔑 <strong>First-time login:</strong> your password is '
            f'<strong style="font-size:1.05rem;text-decoration:underline">{DEFAULT_PASSWORD}</strong>. '
            f'&nbsp;You will be <strong>prompted to change it</strong> on first login.'
            f'</div>',
            unsafe_allow_html=True)

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#             FORCE PASSWORD CHANGE PAGE                         #
# ═══════════════════════════════════════════════════════════════ #
def page_force_change_password():
    render_header(logo=False)
    fid  = st.session_state.faculty_id
    name = st.session_state.faculty_name
    st.markdown(f"### 🔑 Set Your Password")
    st.markdown(
        f"<div style='text-align:center;font-size:1rem;font-weight:600;color:#0b3a67;"
        f"margin-bottom:8px'>Welcome, {name}</div>",
        unsafe_allow_html=True)
    st.info("You must set a new password before continuing. "
            "It must be at least 6 characters and must not be the default password.")
    np1 = st.text_input("New Password", type="password", key="fc_np1")
    np2 = st.text_input("Confirm New Password", type="password", key="fc_np2")
    if st.button("Set Password & Continue", use_container_width=True, type="primary"):
        if len(np1) < 6:
            st.error("Password must be at least 6 characters.")
        elif np1 == DEFAULT_PASSWORD:
            st.error(f"New password cannot be the default password ({DEFAULT_PASSWORD}).")
        elif np1 != np2:
            st.error("Passwords do not match.")
        else:
            pw_update(fid, hash_password(np1), must_change=False)
            st.session_state.must_change_pw = False
            st.success("Password set successfully! Continuing…")
            st.rerun()
    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
    st.stop()


# ═══════════════════════════════════════════════════════════════ #
#            CHANGE PASSWORD SECTION (logged-in user)            #
# ═══════════════════════════════════════════════════════════════ #
def section_change_password():
    fid = st.session_state.faculty_id
    with st.expander("🔑 Change My Password"):
        op  = st.text_input("Current Password", type="password", key="usr_op")
        np1 = st.text_input("New Password (min 6 chars)", type="password", key="usr_np1")
        np2 = st.text_input("Confirm New Password", type="password", key="usr_np2")
        if st.button("Update Password", key="usr_upd_pw"):
            entry = pw_get(fid)
            if not entry or not verify_password(op, entry["password_hash"]):
                st.error("Current password is incorrect.")
            elif len(np1) < 6:
                st.error("New password must be at least 6 characters.")
            elif np1 != np2:
                st.error("Passwords do not match.")
            elif np1 == DEFAULT_PASSWORD:
                st.error(f"Cannot reuse the default password ({DEFAULT_PASSWORD}).")
            else:
                pw_update(fid, hash_password(np1), must_change=False)
                st.success("Password updated successfully.")


# ═══════════════════════════════════════════════════════════════ #
#                        ADMIN VIEW                              #
# ═══════════════════════════════════════════════════════════════ #
def page_admin(fac_df, offline_df, online_df):
    st.markdown(
        '<div class="card"><div class="card-title">🔒 Admin Panel</div>'
        '<p class="card-sub">Full administrative access.</p></div>',
        unsafe_allow_html=True)

    t1, t2, t3, t4, t5, t6 = st.tabs([
        "📋 Willingness Records",
        "🤖 Run Optimizer",
        "📊 View Results",
        "👥 Faculty Accounts",
        "⚙️ Portal Settings",
        "🔄 Duty Swaps",
    ])
    with t6:
        admin_swap_panel(fac_df)

    # ── Tab 1: Willingness Records ──────────────────────────────── #
    with t1:
        # ── Willingness submission status (who has / has not submitted) ──
        st.markdown("### 📌 Willingness Submission Status")
        _fac_rows = db_get_all_faculty()
        _w_rows   = db_get_all_willingness_rows()
        _wcnt = {}
        for _r in _w_rows:
            _k = _norm_id(_r.get("faculty_id", ""))
            _wcnt[_k] = _wcnt.get(_k, 0) + 1
        _stat = []
        for _r in _fac_rows:
            _nm   = str(_r.get("name", "")).strip()
            _code = _map_desig(_r.get("designation", ""))
            _need = FACULTY_WILL_OVERRIDE.get(_norm_name(_nm), DUTY_STRUCTURE.get(_code, 0))
            _got  = _wcnt.get(_norm_id(_r.get("faculty_id", "")), 0)
            _stat.append({
                "ID No.": _r.get("faculty_id", ""), "Name": _nm,
                "Designation": DESIG_FULL.get(_code, _code),
                "Duties": fac_duty_range(_nm, _code)[0],
                "Options Required": _need, "Options Submitted": _got,
                "Status": ("❌ Not Submitted" if _got == 0 else
                           "⚠ Incomplete" if _got < _need else "✅ Submitted"),
            })
        _sdf = pd.DataFrame(_stat)
        if _sdf.empty:
            st.info("No faculty found.")
        else:
            _order = {"❌ Not Submitted": 0, "⚠ Incomplete": 1, "✅ Submitted": 2}
            _rank = {DESIG_FULL.get(c, c): i for i, c in
                     enumerate(["P", "ACP", "SAP", "AP3", "AP2", "TA", "RA"])}
            _sdf = (_sdf.assign(_o=_sdf["Status"].map(_order),
                                _r=_sdf["Designation"].map(_rank).fillna(99))
                        .sort_values(["_o", "_r", "Name"]).drop(columns=["_o", "_r"])
                        .reset_index(drop=True))
            _m1, _m2, _m3, _m4 = st.columns(4)
            _m1.metric("Total", len(_sdf))
            _m2.metric("✅ Submitted", int((_sdf["Status"] == "✅ Submitted").sum()))
            _m3.metric("⚠ Incomplete", int((_sdf["Status"] == "⚠ Incomplete").sum()))
            _m4.metric("❌ Not Submitted", int((_sdf["Status"] == "❌ Not Submitted").sum()))
            _show = st.radio("Show", ["Not Submitted", "Incomplete", "Submitted", "All"],
                             horizontal=True, key="will_status_filter")
            _view = _sdf if _show == "All" else _sdf[_sdf["Status"].str.contains(_show)]
            _view = _view.reset_index(drop=True)
            _view.insert(0, "Sl.No", _view.index + 1)
            st.dataframe(_view, use_container_width=True, hide_index=True)
            _xb = io.BytesIO()
            with pd.ExcelWriter(_xb, engine="openpyxl") as _xw:
                for _sh, _flt in [("Not Submitted", "Not Submitted"), ("Incomplete", "Incomplete"),
                                  ("Submitted", "✅ Submitted"), ("All", None)]:
                    _d = _sdf if _flt is None else _sdf[_sdf["Status"].str.contains(_flt)]
                    _d = _d.reset_index(drop=True)
                    _d.insert(0, "Sl.No", _d.index + 1)
                    _d.to_excel(_xw, sheet_name=_sh, index=False)
            st.download_button(
                "⬇ Download Status (Excel)", data=_xb.getvalue(),
                file_name=f"Willingness_Status_{datetime.date.today():%d-%m-%Y}.xlsx",
                mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                key="dl_will_status")
        st.markdown("---")

        st.markdown("### 📋 Willingness Records")
        st.caption("All willingness submitted by faculty via this portal.")

        w_all = get_all_willingness()
        if w_all.empty:
            st.info("No willingness data collected yet.")
        else:
            vdf = w_all.drop(columns=["FacultyClean"], errors="ignore").reset_index(drop=True)
            if "Sl.No" not in vdf.columns:
                vdf.insert(0, "Sl.No", vdf.index + 1)
            sub_cnt_val = vdf["Faculty"].nunique() if "Faculty" in vdf.columns else 0
            c1, c2, c3 = st.columns(3)
            c1.metric("Faculty Submitted",  sub_cnt_val)
            c2.metric("Not Yet Submitted",  len(fac_df) - sub_cnt_val)
            c3.metric("Total Rows",          len(vdf))
            st.dataframe(vdf, use_container_width=True, hide_index=True)

            st.markdown("#### ⬇ Download Collected Willingness")
            dl1, dl2 = st.columns(2)
            with dl1:
                st.download_button(
                    "⬇ Download as CSV",
                    data=vdf[["Faculty", "Date", "Session"]].to_csv(index=False).encode("utf-8"),
                    file_name="Willingness.csv", mime="text/csv",
                    use_container_width=True)
            with dl2:
                _buf = io.BytesIO()
                vdf[["Faculty", "Date", "Session"]].to_excel(_buf, index=False, engine="openpyxl")
                st.download_button(
                    "⬇ Download as Excel (.xlsx)",
                    data=_buf.getvalue(),
                    file_name="Willingness.xlsx",
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                    use_container_width=True)

        st.markdown("---")
        st.markdown("#### 🗑 Reset Portal Data")
        st.caption("Use these buttons at the start of a new exam cycle. Each action is permanent.")

        rc1, rc2 = st.columns(2)
        with rc1:
            st.markdown("**Delete Willingness Only**")
            st.checkbox("Confirm delete willingness", key="confirm_delete_will")
            if st.button("🗑 Delete All Willingness", type="primary",
                         use_container_width=True, key="btn_del_will"):
                if st.session_state.get("confirm_delete_will"):
                    _left = db_clear_all_willingness()
                    if _left:
                        st.error(f"❌ {_left} willingness row(s) could not be deleted.")
                        st.markdown(_RLS_HELP)
                    else:
                        st.success("✅ All willingness deleted.")
                        del st.session_state["confirm_delete_will"]
                        st.rerun()
                else:
                    st.error("Tick the confirmation checkbox first.")

        with rc2:
            st.markdown("**Delete Allotment Only**")
            st.checkbox("Confirm delete allotment", key="confirm_delete_allot")
            if st.button("🗑 Delete All Allotment", type="primary",
                         use_container_width=True, key="btn_del_allot"):
                if st.session_state.get("confirm_delete_allot"):
                    _left = db_clear_allocation()
                    if _left:
                        st.error(f"❌ {_left} allotment row(s) could not be deleted.")
                        st.markdown(_RLS_HELP)
                    else:
                        st.success("✅ All allotment records deleted.")
                        del st.session_state["confirm_delete_allot"]
                        st.rerun()
                else:
                    st.error("Tick the confirmation checkbox first.")

        st.markdown("---")
        st.markdown("**Delete One Faculty's Willingness** (e.g. test entries)")
        _wrows = db_get_all_willingness_rows()
        _wfac = {}
        for _r in _wrows:
            _k = str(_r.get("faculty_id", "")).strip()
            if _k:
                _nm, _c = _wfac.get(_k, (str(_r.get("faculty_name", "")).strip(), 0))
                _wfac[_k] = (_nm, _c + 1)
        if not _wfac:
            st.caption("No willingness submissions in the database.")
        else:
            _opts = sorted(_wfac, key=lambda k: _wfac[k][0].lower())
            _pick = st.selectbox(
                "Select faculty", _opts, key="del_one_will_pick",
                format_func=lambda k: f"{_wfac[k][0]} ({k}) — {_wfac[k][1]} option(s)")
            if st.button("🗑 Delete This Faculty's Willingness",
                         use_container_width=True, key="btn_del_one_will"):
                _left = db_delete_willingness_for(_pick)
                if _left:
                    st.error(f"❌ {_left} row(s) could not be deleted.")
                    st.markdown(_RLS_HELP)
                else:
                    st.success(f"✅ Willingness deleted for {_wfac[_pick][0]} ({_pick}).")
                    st.rerun()

        st.markdown("---")
        st.markdown("**Full Reset — Delete Both Willingness & Allotment**")
        st.caption("Use this to completely reset before a new examination cycle.")
        st.checkbox("I confirm full reset of all willingness and allotment data",
                    key="confirm_full_reset")
        if st.button("⚠ Full Reset (Willingness + Allotment)", type="primary",
                     use_container_width=True, key="btn_full_reset"):
            if st.session_state.get("confirm_full_reset"):
                _left = db_clear_all_willingness() + db_clear_allocation()
                if _left:
                    st.error(f"❌ {_left} row(s) could not be deleted.")
                    st.markdown(_RLS_HELP)
                else:
                    st.success("✅ Full reset complete — all willingness and allotment records deleted.")
                    del st.session_state["confirm_full_reset"]
                    st.rerun()
            else:
                st.error("Tick the confirmation checkbox first.")

    # ── Tab 2: Run Optimizer ─────────────────────────────────────── #
    with t2:
        st.markdown("### 🤖 Run Allocation Optimizer")
        st.info("ℹ️ Online duty is suspended this semester. All duties are offline only.")
        st.markdown("#### 📁 Data Source Status (Supabase)")
        _w_all  = get_all_willingness()
        _wrows  = len(_w_all)
        _wfac   = _w_all["Faculty"].nunique() if not _w_all.empty and "Faculty" in _w_all.columns else 0
        _off_ok = len(offline_df) > 0
        st.markdown(f"""
| Source | Purpose | Status |
|---|---|---|
| Supabase `faculty` | Faculty list + designations | ✅ {len(fac_df)} records |
| Supabase `offline_duty` | Offline exam slots | {"✅ " + str(len(offline_df)) + " slots" if _off_ok else "❌ No data"} |
| Supabase `willingness`  | Faculty willingness | ✅ {_wrows} rows, {_wfac} faculty |
""")
        c1, c2, c3 = st.columns(3)
        c1.metric("Total Faculty",         len(fac_df))
        c2.metric("Willingness Submitted", f"{_wfac}/{len(fac_df)}")
        c3.metric("Willingness Rows",      _wrows)

        if not _off_ok:
            st.error("No offline duty slots in Supabase. Run load_to_supabase.py.")
        elif not ORTOOLS_OK and not SCIPY_OK:
            st.error("No solver available. Run:  pip install ortools  OR  pip install scipy")
        else:
            solver_label = "OR-Tools CP-SAT ✅" if ORTOOLS_OK else "scipy HiGHS (fallback) ⚠"
            st.info(f"🔧 Active solver: **{solver_label}**"
                    + ("" if ORTOOLS_OK else
                       " — install OR-Tools for better results:  `pip install ortools`"))

            st.markdown("#### 🔍 Pre-Run Diagnostic")
            diag_wdf        = get_all_willingness()
            slot_dates_diag = set(offline_df["Date"].dt.date.dropna())

            if not diag_wdf.empty and slot_dates_diag:
                wdf_diag = diag_wdf.copy()
                wdf_diag["_date"] = to_dt(
                    wdf_diag["Date"]).dt.date
                will_dates_diag = set(wdf_diag["_date"].dropna())
                overlap_diag    = will_dates_diag & slot_dates_diag
                only_will_diag  = will_dates_diag - slot_dates_diag

                d1, d2, d3 = st.columns(3)
                d1.metric("Slot Dates",        len(slot_dates_diag))
                d2.metric("Willingness Dates", len(will_dates_diag))
                d3.metric("✅ Overlapping",     len(overlap_diag),
                          delta="⚠ ZERO — dates don't match!" if len(overlap_diag) == 0 else None,
                          delta_color="inverse" if len(overlap_diag) == 0 else "off")

                if len(overlap_diag) == 0:
                    st.error("🚨 **CRITICAL: Zero date overlap!** Willingness dates don't match any exam slots.")
                elif len(only_will_diag) > len(overlap_diag):
                    st.warning(f"⚠️ {len(only_will_diag)} willingness dates outside slot period "
                               f"(only {len(overlap_diag)}/{len(will_dates_diag)} overlap).")
                else:
                    st.success(f"✅ {len(overlap_diag)} overlapping dates — good coverage.")

                if only_will_diag:
                    with st.expander(f"📋 {len(only_will_diag)} willingness dates NOT in any slot"):
                        bad = wdf_diag[wdf_diag["_date"].isin(only_will_diag)]\
                            .drop(columns=["_date", "FacultyClean"], errors="ignore")\
                            .reset_index(drop=True)
                        st.dataframe(bad, use_container_width=True, hide_index=True)
            else:
                st.info("Upload willingness and ensure slot files exist to run diagnostic.")

            st.markdown("---")
            st.info("💡 Recommended: Disable allotment view (Portal Settings) before running.")
            if st.button("▶ Run Optimizer", type="primary", use_container_width=True):
                lb2 = st.empty()
                with st.spinner("Running MILP optimization…"):
                    try:
                        alloc_out, sumdf_out, slotdf_out, _ = run_optimizer(lb2)
                        st.success("✅ Optimization complete! Go to **📊 View Results** to review.")
                        st.balloons()
                    except Exception as e:
                        import traceback
                        st.error(f"Optimizer error: {e}")
                        st.code(traceback.format_exc(), language="text")

    # ── Tab 3: View Results ─────────────────────────────────────── #
    with t3:
        admin_final_allotment(fac_df, offline_df)
        st.markdown("---")
        st.markdown("### 📊 Allocation Results")

        pct_m   = st.session_state.get("pct_milp",    None)
        pct_g   = st.session_state.get("pct_greedy",  None)
        unmet_m = st.session_state.get("unmet_milp",  None)
        unmet_g = st.session_state.get("unmet_greedy",None)
        rec     = st.session_state.get("recommended", "MILP")

        if pct_m is not None and pct_g is not None:
            st.markdown("#### ⚖️ Method Comparison")
            c1, c2 = st.columns(2)
            def method_card(col, name, pct, unmet, is_rec):
                bg   = "#d1fae5" if is_rec else "#f1f5f9"
                bdr  = "#6ee7b7" if is_rec else "#e2e8f0"
                badge = " ⭐ Recommended" if is_rec else ""
                col.markdown(f"""
<div style="background:{bg};border:2px solid {bdr};border-radius:12px;
            padding:16px 18px;text-align:center">
  <div style="font-size:1.05rem;font-weight:800;color:#0f172a">{name}{badge}</div>
  <div style="font-size:2rem;font-weight:900;color:#0b3a67;margin:8px 0">{pct:.1f}%</div>
  <div style="font-size:.85rem;color:#475569">Willingness Match</div>
  <div style="margin-top:8px;font-size:.9rem;color:{'#065f46' if unmet==0 else '#991b1b'};font-weight:700">
    {'✅ All slots filled' if unmet==0 else f'⚠ {unmet} slot(s) unmet'}
  </div>
</div>""", unsafe_allow_html=True)

            with c1: method_card(c1, "Method A — MILP",   pct_m, unmet_m, rec=="MILP")
            with c2: method_card(c2, "Method B — Greedy", pct_g, unmet_g, rec=="Greedy")

            chosen = st.radio(
                "**Select method to activate as Final Allocation:**",
                ["Method A — MILP", "Method B — Greedy"],
                index=0 if rec=="MILP" else 1,
                horizontal=True, key="method_choice")

            if st.button("✅ Apply Selected Method", type="primary", use_container_width=True):
                chosen_key = "MILP" if "MILP" in chosen else "Greedy"
                sel_alloc  = st.session_state.get(f"alloc_{chosen_key.lower()}")
                sel_sumdf  = st.session_state.get(f"sumdf_{chosen_key.lower()}")
                sel_slotdf = st.session_state.get(f"slotdf_{chosen_key.lower()}")
                if sel_alloc is not None:
                    _recs = []
                    for _, _ar in sel_alloc.iterrows():
                        _nm = str(_ar.get("Name","")).strip()
                        _fid_match = fac_df[fac_df["Name"].str.strip().str.lower() == _nm.lower()]
                        _fid_val   = str(_fid_match.iloc[0]["ID No."]) if not _fid_match.empty else _nm
                        _recs.append({
                            "faculty_id":   _fid_val,
                            "faculty_name": _nm,
                            "designation":  str(_ar.get("Designation","")),
                            "duty_date":    str(to_dt(_ar["Date"]).date()),
                            "session":      str(_ar.get("Session","")).strip().upper(),
                            "duty_type":    str(_ar.get("Type","Offline")).strip(),
                            "allocated_by": str(_ar.get("Allocated_By","")).strip(),
                        })
                    db_save_allocation(_recs)
                    sel_alloc.to_excel(FINAL_ALLOC_FILE, index=False)
                    with pd.ExcelWriter(ALLOC_REPORT_FILE, engine="openpyxl") as writer:
                        sel_alloc.to_excel(writer,  sheet_name="Full_Allocation",   index=False)
                        sel_sumdf.to_excel(writer,  sheet_name="Faculty_Summary",   index=False)
                        sel_slotdf.to_excel(writer, sheet_name="Slot_Verification", index=False)
                    st.success(f"✅ {chosen_key} method saved to Supabase and Excel.")
                    st.session_state["recommended"] = chosen_key
                    st.rerun()

            st.markdown("#### ⬇ Download Both Results")
            dl1, dl2 = st.columns(2)
            with dl1:
                fp = "Final_Allocation_MILP.xlsx"
                if os.path.exists(fp):
                    with open(fp, "rb") as fh:
                        st.download_button("⬇ MILP Allocation", data=fh.read(),
                            file_name=fp, use_container_width=True,
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            with dl2:
                fp = "Final_Allocation_Greedy.xlsx"
                if os.path.exists(fp):
                    with open(fp, "rb") as fh:
                        st.download_button("⬇ Greedy Allocation", data=fh.read(),
                            file_name=fp, use_container_width=True,
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            st.markdown("---")

        _db_alloc_rows = db_get_all_allocation()
        if _db_alloc_rows:
            av = pd.DataFrame(_db_alloc_rows)
            av.rename(columns={"faculty_name":"Name","duty_date":"Date","session":"Session",
                                "duty_type":"Type","allocated_by":"Allocated_By",
                                "designation":"Designation"}, inplace=True)
            av["Date"] = pd.to_datetime(av["Date"], errors="coerce").dt.strftime("%d-%m-%Y")
        elif os.path.exists(FINAL_ALLOC_FILE):
            av = pd.read_excel(FINAL_ALLOC_FILE)
        else:
            av = pd.DataFrame()

        if av.empty:
            st.info("No results yet. Run the optimizer first.")
        else:
            rep = {}
            if os.path.exists(ALLOC_REPORT_FILE):
                xl2 = pd.ExcelFile(ALLOC_REPORT_FILE)
                for sh in xl2.sheet_names: rep[sh] = xl2.parse(sh)

            tot2 = len(av)
            if tot2 > 0 and "Allocated_By" in av.columns:
                ab3    = av["Allocated_By"]
                will_m = int(ab3.isin(WILL_TAGS).sum())
                aut    = int(ab3.isin(["Auto-Assigned","OR-Assigned","Gap-Fill"]).sum())
                c1, c2, c3, c4 = st.columns(4)
                c1.metric("Total Assignments",   tot2)
                c2.metric("Willingness Matched", will_m)
                c3.metric("Auto-Assigned",        aut)
                c4.metric("Overall Match %",      f"{will_m/tot2*100:.1f}%")

            for sh_name, label in [("Designation_Summary","Designation Summary"),
                                   ("Slot_Verification",  "Slot Verification"),
                                   ("Faculty_Summary",    "Faculty Summary")]:
                if sh_name in rep:
                    st.markdown(f"#### {label}")
                    if sh_name == "Slot_Verification" and "Status" in rep[sh_name].columns:
                        um = rep[sh_name][~rep[sh_name]["Status"].str.startswith("✓")]
                        ts = len(rep[sh_name]); ms2 = ts - len(um)
                        if len(um) == 0:
                            st.metric("Slots Fulfilled", f"{ms2}/{ts}", delta="✅ All Slots Met")
                        else:
                            st.metric("Slots Fulfilled", f"{ms2}/{ts}",
                                      delta=f"⚠ {len(um)} unmet", delta_color="inverse")
                            for _, r in um.iterrows():
                                st.error(f"⚠ {r['Date']} {r['Session']} {r['Type']} — {r['Status']}")
                    st.dataframe(rep[sh_name], use_container_width=True, hide_index=True)

            st.markdown("---")
            st.markdown("#### 🔍 Per-Faculty Deviation Analysis")
            admin_fnames = fac_df["Name"].dropna().drop_duplicates().tolist()
            admin_sel    = st.selectbox("Select Faculty", admin_fnames, key="admin_dev_sel")
            admin_sc     = clean(admin_sel)
            wd_admin     = load_willingness()
            admin_will_set = set()
            if not wd_admin.empty:
                wm_a = fac_mask(wd_admin, admin_sc)
                wr_a = wd_admin[wm_a]
                if not wr_a.empty and {"Date","Session"}.issubset(wr_a.columns):
                    for d2, s2 in zip(wr_a["Date"], wr_a["Session"]):
                        nd = to_dt(d2)
                        if pd.notna(nd):
                            admin_will_set.add((nd.date(), str(s2).upper()))
            am_a = fac_mask(av, admin_sc)
            render_deviation_section(av[am_a].copy(), admin_will_set)

            st.markdown("---")
            st.markdown("#### Full Allocation Table")
            st.dataframe(av, use_container_width=True, hide_index=True)
            col1, col2 = st.columns(2)
            with col1:
                if os.path.exists(FINAL_ALLOC_FILE):
                    with open(FINAL_ALLOC_FILE, "rb") as fh:
                        st.download_button("⬇ Final_Allocation.xlsx", data=fh.read(),
                            file_name="Final_Allocation.xlsx",
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            with col2:
                if os.path.exists(ALLOC_REPORT_FILE):
                    with open(ALLOC_REPORT_FILE, "rb") as fh:
                        st.download_button("⬇ Allocation_Report.xlsx", data=fh.read(),
                            file_name="Allocation_Report.xlsx",
                            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

    # ── Tab 4: Faculty Accounts ─────────────────────────────────── #
    with t4:
        st.markdown("### 👥 Faculty Account Management")
        st.caption("View all faculty accounts, reset passwords, and manage admin rights.")

        all_fac_rows = db_get_all_faculty()
        id_name_map  = {r["faculty_id"]: r["name"] for r in all_fac_rows}
        acc_rows = []
        for r in all_fac_rows:
            acc_rows.append({
                "ID No.":          r["faculty_id"],
                "Name":            r["name"],
                "Raw Designation": r["designation"],
                "Resolved Code":   _map_desig(r["designation"]) if clean(r["name"]) not in FACULTY_DESIG_OVERRIDE
                                   else f"{FACULTY_DESIG_OVERRIDE[clean(r['name'])]} ⚠️override",
                "Full Name":       DESIG_FULL.get(_map_desig(r["designation"]), "Unknown") if clean(r["name"]) not in FACULTY_DESIG_OVERRIDE
                                   else DESIG_FULL.get(FACULTY_DESIG_OVERRIDE[clean(r["name"])], "Unknown"),
                "Must Change":     "⚠ Yes" if r.get("must_change_pw") else "No",
                "Is Admin":        "👑 Yes" if r.get("is_admin") else "No",
            })
        acc_df = pd.DataFrame(acc_rows)
        acc_df.insert(0, "Sl.No", acc_df.index + 1)
        st.dataframe(acc_df, use_container_width=True, hide_index=True)

        st.markdown("---")
        st.markdown("#### 📥 Replace Faculty & Research Scholar List")
        st.caption("Upload the new Excel (faculty + research scholars). The portal list becomes "
                   "exactly this Excel: new names are added, changed names are updated, and "
                   "names not in the Excel are removed.")
        _up = st.file_uploader("New faculty list (.xlsx)", type=["xlsx", "xls"],
                               accept_multiple_files=True, key="fac_sync_upload")
        if _up:
            try:
                _new = parse_faculty_excels(_up)
            except Exception as _e:
                st.error(f"Could not read the file: {_e}")
                _new = {}
            if _new:
                _me = _norm_id(st.session_state.get("_logged_fid", ""))
                _plan = plan_faculty_sync(_new, all_fac_rows)
                _remove = [r for r in _plan["missing"] if _norm_id(r["faculty_id"]) != _me]
                st.info(f"**{len(_new)}** names in the Excel  →  "
                        f"**{len(_plan['add'])}** added · **{len(_plan['update'])}** updated · "
                        f"**{len(_remove)}** old names removed")
                if _remove:
                    with st.expander("See names that will be removed"):
                        st.write(", ".join(f"{r['name']} ({r['faculty_id']})" for r in _remove))
                if st.button("✅ Replace Faculty List", type="primary",
                             use_container_width=True, key="btn_fac_sync"):
                    _err = []
                    _h = hash_password(DEFAULT_PASSWORD)
                    for _r in _plan["add"]:
                        try:
                            _sb().table("faculty").insert({**_r, "password_hash": _h,
                                "must_change_pw": True, "is_admin": False}).execute()
                        except Exception as _e:
                            _err.append(f"Add {_r['faculty_id']}: {_e}")
                    for _r in _plan["update"]:
                        _f = {k: v for k, v in _r.items() if k not in ("faculty_id", "old_name")}
                        try:
                            _sb().table("faculty").update(_f).eq("faculty_id", _r["faculty_id"]).execute()
                        except Exception as _e:
                            _err.append(f"Update {_r['faculty_id']}: {_e}")
                    for _r in _remove:
                        try:
                            for _t in ("willingness", "final_allocation"):
                                _sb().table(_t).delete().eq("faculty_id", _r["faculty_id"]).execute()
                            _sb().table("faculty").delete().eq("faculty_id", _r["faculty_id"]).execute()
                        except Exception as _e:
                            _err.append(f"Remove {_r['faculty_id']}: {_e}")
                    st.cache_data.clear()
                    # Verify against the database (RLS can silently ignore writes)
                    _after = plan_faculty_sync(_new, db_get_all_faculty())
                    _pending = (len(_after["add"]) + len(_after["update"]) +
                                len([r for r in _after["missing"] if _norm_id(r["faculty_id"]) != _me]))
                    if _err:
                        st.error("Some changes failed:\n\n" + "\n\n".join(_err[:10]))
                    if _pending:
                        st.error(f"❌ {_pending} change(s) did not reach Supabase (Row Level Security). "
                                 "Run this once in Supabase → SQL Editor, then upload again:")
                        st.code('create policy "admin insert faculty" on faculty for insert with check (true);\n'
                                'create policy "admin update faculty" on faculty for update using (true);\n'
                                'create policy "admin delete faculty" on faculty for delete using (true);',
                                language="sql")
                    else:
                        st.success(f"✅ Faculty list replaced — {len(_new)} names now in the portal.")

        st.markdown("---")
        st.markdown("#### 🔑 Reset a Faculty's Password")
        st.caption(f"Resets password to default (**{DEFAULT_PASSWORD}**) and forces change on next login.")
        id_options = [f"{fid} — {nm}" for fid, nm in id_name_map.items()]
        reset_sel  = st.selectbox("Select Faculty to Reset", id_options, key="admin_reset_sel")
        reset_fid  = reset_sel.split(" — ")[0]
        if st.button("Reset Password", key="btn_reset_pw"):
            db_reset_faculty_pw(reset_fid)
            st.success(f"Password for **{id_name_map.get(reset_fid, reset_fid)}** reset to default.")

        st.markdown("---")
        st.markdown("#### 🔄 Reset ALL Faculty Passwords in One Go")
        st.caption(f"Resets every faculty's password to **{DEFAULT_PASSWORD}** and forces a change on next login. "
                   f"Use at the start of a new semester before faculty begin logging in.")
        _col_warn, _col_btn = st.columns([3, 1])
        with _col_warn:
            st.warning("⚠️ This will log out and force password change for **all** faculty. "
                       "Only proceed if you are sure.")
        st.checkbox("I confirm bulk reset of all faculty passwords", key="confirm_bulk_pw_reset")
        if st.button("🔄 Reset ALL Passwords Now", type="primary",
                     use_container_width=True, key="btn_bulk_reset_pw"):
            if st.session_state.get("confirm_bulk_pw_reset"):
                _reset_h = hash_password(DEFAULT_PASSWORD)
                _all_rows = db_get_all_faculty()
                _count = 0
                for _r in _all_rows:
                    _sb().table("faculty").update({
                        "password_hash": _reset_h, "must_change_pw": True
                    }).eq("faculty_id", _r["faculty_id"]).execute()
                    _count += 1
                del st.session_state["confirm_bulk_pw_reset"]
                st.success(f"✅ {_count} faculty passwords reset to **{DEFAULT_PASSWORD}**. "
                           f"All faculty will be prompted to change on next login.")
                st.rerun()
            else:
                st.error("Tick the confirmation checkbox first.")

        st.markdown("---")
        st.markdown("#### 👑 Toggle Admin Rights")
        toggle_sel  = st.selectbox("Select Faculty", id_options, key="admin_toggle_sel")
        toggle_fid  = toggle_sel.split(" — ")[0]
        toggle_row  = db_get_faculty_by_id(toggle_fid)
        cur_admin   = toggle_row.get("is_admin", False) if toggle_row else False
        st.info(f"**{id_name_map.get(toggle_fid, toggle_fid)}** is currently: "
                f"{'👑 Admin' if cur_admin else 'Regular Faculty'}")
        col_a, col_b = st.columns(2)
        with col_a:
            if st.button("Grant Admin", disabled=cur_admin, use_container_width=True):
                db_set_admin(toggle_fid, True)
                st.success(f"Admin rights granted to {id_name_map.get(toggle_fid, toggle_fid)}."); st.rerun()
        with col_b:
            if st.button("Revoke Admin", disabled=not cur_admin, use_container_width=True):
                db_set_admin(toggle_fid, False)
                st.success(f"Admin rights revoked from {id_name_map.get(toggle_fid, toggle_fid)}."); st.rerun()

        st.markdown("---")
        st.markdown("#### 🔒 Change My Admin Password")
        with st.expander("Change Admin Password"):
            op  = st.text_input("Current Password", type="password", key="adm_op")
            np1 = st.text_input("New Password", type="password", key="adm_np1")
            np2 = st.text_input("Confirm New Password", type="password", key="adm_np2")
            if st.button("Update Admin Password", key="adm_upd_pw"):
                entry = pw_get(st.session_state.faculty_id)
                if not entry or not verify_password(op, entry["password_hash"]):
                    st.error("Current password is incorrect.")
                elif len(np1) < 6:
                    st.error("Password must be at least 6 characters.")
                elif np1 != np2:
                    st.error("Passwords do not match.")
                else:
                    pw_update(st.session_state.faculty_id, hash_password(np1))
                    st.success("Admin password updated successfully.")

    # ── Tab 5: Portal Settings ──────────────────────────────────── #
    with t5:
        st.markdown("### ⚙️ Portal Settings")
        st.markdown("---")
        st.markdown("#### 🔒 Allotment View — User Access Control")
        is_open = gate_is_open()
        if is_open:
            st.markdown(
                "<div style='background:#d1fae5;border:1.5px solid #6ee7b7;"
                "border-radius:10px;padding:12px 18px;margin-bottom:14px'>"
                "<span style='font-size:1.05rem;font-weight:700;color:#065f46'>"
                "🟢  Allotment view is ENABLED — faculty can see their allotment.</span>"
                "</div>", unsafe_allow_html=True)
        else:
            st.markdown(
                "<div style='background:#fee2e2;border:1.5px solid #fca5a5;"
                "border-radius:10px;padding:12px 18px;margin-bottom:14px'>"
                "<span style='font-size:1.05rem;font-weight:700;color:#991b1b'>"
                "🔴  Allotment view is DISABLED — faculty see a waiting message.</span>"
                "</div>", unsafe_allow_html=True)
        en_col, dis_col = st.columns(2)
        with en_col:
            if st.button("✅ Enable Allotment View", use_container_width=True,
                         disabled=is_open, type="primary"):
                set_gate(True); st.success("Enabled."); st.rerun()
        with dis_col:
            if st.button("🔴 Disable Allotment View", use_container_width=True,
                         disabled=not is_open):
                set_gate(False); st.warning("Disabled."); st.rerun()
        st.caption("Workflow: Disable → Run Optimizer → Review → Enable.")

        st.markdown("---")
        st.markdown("#### 📅 Upload Duty Slots (Exam Schedule)")
        st.caption("Upload the End-Semester duty requirement. Faculty can select willingness only "
                   "on these dates. Uploading replaces ALL existing slots (including old semesters).")
        _tmpl = io.BytesIO()
        pd.DataFrame({"Date": ["16-11-2026", "17-11-2026"], "FN": [10, 12], "AN": [8, 9]}
                     ).to_excel(_tmpl, index=False)
        st.download_button("⬇ Template (Date | FN | AN)", data=_tmpl.getvalue(),
                           file_name="Duty_Slots_Template.xlsx", key="dl_slot_tmpl")
        _sf = st.file_uploader("Duty slot Excel (.xlsx)", type=["xlsx", "xls"], key="slot_upload")
        if _sf:
            try:
                _slots = parse_slot_excel(_sf)
            except Exception as _e:
                st.error(f"Could not read the file: {_e}")
                _slots = []
            if _slots:
                _out = [x for x in _slots
                        if not _in_semester_window(x["duty_date"])]
                _sdf = pd.DataFrame(_slots)
                _sdf["Day"] = pd.to_datetime(_sdf["duty_date"]).dt.strftime("%a")
                _sdf["Date"] = pd.to_datetime(_sdf["duty_date"]).dt.strftime("%d-%m-%Y")
                _piv = (_sdf.pivot_table(index=["Date", "Day"], columns="session",
                                         values="required", aggfunc="sum", fill_value=0)
                        .reset_index())
                _piv["_d"] = pd.to_datetime(_piv["Date"], format="%d-%m-%Y")
                _piv = _piv.sort_values("_d").drop(columns="_d")
                st.info(f"**{_sdf['duty_date'].nunique()}** exam days · **{len(_slots)}** sessions · "
                        f"**{int(_sdf['required'].sum())}** total duties")
                st.dataframe(_piv, use_container_width=True, hide_index=True)
                if _out:
                    st.error(f"❌ {len(_out)} row(s) are outside "
                             f"{SEMESTER_CAL_START:%d-%m-%Y} – {SEMESTER_CAL_END:%d-%m-%Y}. "
                             "Check the dates (DD-MM-YYYY) and upload again.")
                elif st.button("✅ Replace Duty Slots", type="primary",
                               use_container_width=True, key="btn_slot_upload"):
                    _left = _db_delete_all("offline_duty")
                    if _left:
                        st.error(f"❌ Old slots could not be deleted ({_left} left). Run once in "
                                 "Supabase → SQL Editor:")
                        st.code('create policy "admin delete slots" on offline_duty for delete using (true);\n'
                                'create policy "admin insert slots" on offline_duty for insert with check (true);',
                                language="sql")
                    else:
                        try:
                            _sb().table("offline_duty").insert(_slots).execute()
                            st.cache_data.clear()
                            _n = _db_count("offline_duty")
                            if _n == len(_slots):
                                st.success(f"✅ {_n} duty sessions uploaded. Faculty can now select dates.")
                            else:
                                st.error(f"❌ Only {_n} of {len(_slots)} sessions were saved.")
                        except Exception as _e:
                            st.error(f"❌ Upload failed: {_e}")

        st.markdown("---")
        st.markdown("#### 🔄 Clear App Cache")
        st.caption("Forces a reload of faculty, slots, and willingness data from Supabase. "
                   "Use after updating designations in Supabase or after applying overrides.")
        if st.button("🔄 Clear All Cached Data", use_container_width=True):
            st.cache_data.clear()
            st.success("✅ Cache cleared — all data will reload fresh from Supabase.")
            st.rerun()




# ═══════════════════════════════════════════════════════════════ #
#             ALLOTMENT VIEW (faculty self-service)              #
# ═══════════════════════════════════════════════════════════════ #
def admin_final_allotment(fac_df, offline_df):
    st.markdown("### 📌 Final Allotment (what faculty see)")
    _live = db_get_all_allocation()
    _open = gate_is_open()
    c1, c2, c3 = st.columns(3)
    c1.metric("Duties in final allotment", len(_live))
    c2.metric("Faculty / scholars with duty", len({_norm_id(a.get('faculty_id')) for a in _live}))
    c3.metric("Visible to faculty", "Yes" if _open else "No")
    g1, g2 = st.columns(2)
    if g1.button("👁 Publish to faculty", use_container_width=True, disabled=_open or not _live,
                 key="fa_pub"):
        set_gate(True); st.rerun()
    if g2.button("🙈 Hide from faculty", use_container_width=True, disabled=not _open, key="fa_hide"):
        set_gate(False); st.rerun()

    # ── Download for authorities ───────────────────────────────
    if _live:
        st.download_button(
            "⬇ Download Final Allotment for Authorities (Excel)",
            data=build_authority_excel(_live, db_get_all_faculty(), offline_df),
            file_name=f"Final_Invigilation_Allotment_{datetime.date.today():%d-%m-%Y}.xlsx",
            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
            type="primary", use_container_width=True, key="dl_authority")
        st.caption("Faculty and research scholars together · sheets: Faculty-wise, Date-wise, "
                   "Session Summary · includes every approved swap.")

    # ── Upload manually corrected allotment ────────────────────
    with st.expander("📤 Upload final allotment (after manual changes)", expanded=not _live):
        st.caption("Upload the corrected allotment Excel — the file downloaded from this app "
                   "(Final_Allocation / Allocation_Report / authorities file) after your edits. "
                   "It needs Name (or ID No.), Date and Session columns. "
                   "This REPLACES the allotment faculty see, and closes any open swap requests.")
        _f = st.file_uploader("Final allotment (.xlsx)", type=["xlsx", "xls"], key="fa_upload")
        if _f:
            try:
                _recs, _errs = parse_final_allotment(_f, fac_df)
            except Exception as _e:
                _recs, _errs = [], [f"Could not read the file: {_e}"]
            _chk = check_allotment(_recs, fac_df, offline_df) if _recs else {"errors": [], "warnings": []}
            _errs = _errs + _chk["errors"]
            st.info(f"**{len(_recs)}** duties read for "
                    f"**{len({r['faculty_id'] for r in _recs})}** faculty / scholars.")
            if _errs:
                st.error(f"❌ {len(_errs)} problem(s) — fix these in the Excel and upload again:")
                st.markdown("\n".join(f"- {e}" for e in _errs[:40]))
            if _chk["warnings"]:
                with st.expander(f"⚠ {len(_chk['warnings'])} item(s) to review "
                                 "(allowed, since you changed them manually)"):
                    st.markdown("\n".join(f"- {w}" for w in _chk["warnings"]))
            elif _recs and not _errs:
                st.success("✔ Every session matches the duty schedule and every person has "
                           "their expected number of duties.")
            if _recs and not _errs:
                _ok = st.checkbox("I confirm this is the final allotment", key="fa_confirm")
                if st.button("✅ Replace Final Allotment", type="primary", disabled=not _ok,
                             use_container_width=True, key="fa_apply"):
                    try:
                        db_save_allocation(_recs)
                        _n = len(db_get_all_allocation())
                        try:
                            for _sw in db_swaps_all():
                                if _sw.get("status") in SWAP_OPEN_STATUSES:
                                    db_swap_update(_sw["id"], {"status": "superseded",
                                        "admin_note": "Closed: final allotment re-uploaded"})
                        except Exception:
                            pass
                        if _n == len(_recs):
                            st.success(f"✅ Final allotment saved ({_n} duties). "
                                       "Click 'Publish to faculty' when ready.")
                        else:
                            st.error(f"❌ Only {_n} of {len(_recs)} duties were saved — check "
                                     "Row Level Security on final_allocation.")
                    except Exception as _e:
                        st.error(f"❌ Save failed: {_e}")


def section_swap(fac_df, my_fid: str, preview: bool = False):
    """Faculty side of duty swap — shown on My Allotment once allotment is published."""
    st.markdown("---")
    st.markdown("### 🔄 Duty Swap — Mutual Adjustment")
    st.caption("Exchange one of your duties with a colleague after discussing it with them. "
               "Either of you can submit the swap; it goes directly to the Examination "
               "Committee for approval. Both of you keep the same number of duties.")
    try:
        swaps = db_swaps_all()
    except Exception:
        st.info("Duty swap is not enabled yet. Please contact the Examination Committee.")
        return
    me     = _norm_id(my_fid)
    allocs = db_get_all_allocation()
    people = _swap_people(fac_df)
    if me not in people:
        st.info("Your record was not found for swapping. Contact admin.")
        return
    by_id  = {str(a.get("id")): a for a in allocs}

    # ── 2. My swap history ──────────────────────────────────────
    mine = [s for s in swaps if me in (_norm_id(s.get("requester_id")), _norm_id(s.get("partner_id")))]
    if mine:
        st.markdown("#### 📄 Swap requests involving you")
        rows = []
        for s in mine:
            i_req = _norm_id(s.get("requester_id")) == me
            rows.append({
                "Swap #": s["id"],
                "With": s["partner_name"] if i_req else s["requester_name"],
                "You give": _duty_txt(s["req_date"], s["req_session"]) if i_req
                            else _duty_txt(s["partner_date"], s["partner_session"]),
                "You take": _duty_txt(s["partner_date"], s["partner_session"]) if i_req
                            else _duty_txt(s["req_date"], s["req_session"]),
                "Status": SWAP_STATUS_LABEL.get(s.get("status"), s.get("status")),
            })
        st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)
        cancellable = [s for s in mine if _norm_id(s.get("requester_id")) == me
                       and s.get("status") in SWAP_OPEN_STATUSES]
        if cancellable:
            cx = st.selectbox("Cancel a request", [s["id"] for s in cancellable],
                              format_func=lambda i: f"Swap #{i}", key="sw_cancel_pick")
            if st.button("↩ Cancel this request", key="sw_cancel_btn", disabled=preview):
                db_swap_update(cx, {"status": "cancelled"})
                st.rerun()

    # ── 3. Find an easy match ───────────────────────────────────
    st.markdown("#### 🔍 Find swap partners")
    today = datetime.date.today()
    lock  = _locked_alloc_ids(swaps)
    my_duties = sorted([a for a in allocs if _norm_id(a.get("faculty_id")) == me
                        and _alloc_date(a) and _alloc_date(a) > today
                        and str(a.get("id")) not in lock],
                       key=lambda a: (_alloc_date(a), str(a.get("session"))))
    if not my_duties:
        st.caption("No upcoming duty available to swap (past duties and duties already in a "
                   "pending swap are not listed).")
        return
    pick = st.selectbox("Your duty to swap", [str(a["id"]) for a in my_duties],
                        format_func=lambda i: _duty_txt(by_id[i]["duty_date"], by_id[i]["session"]),
                        key="sw_my_duty")
    my_alloc = by_id[pick]
    cands = swap_candidates(me, my_alloc, allocs, people, swaps, _will_by_fid())
    if not cands:
        st.warning("No colleague can swap this duty without breaking a rule "
                   "(valuation / exam / lab dates, or one duty per day).")
        return
    n_p = sum(c["level"] == "perfect" for c in cands)
    n_g = sum(c["level"] == "good" for c in cands)
    st.caption(f"{len(cands)} possible partner(s): 🟢 {n_p} perfect · 🟡 {n_g} good · "
               f"⚪ {len(cands) - n_p - n_g} possible. "
               "🟢 = both of you had chosen each other's slot in willingness; "
               "🟡 = one of you had.")
    lv = st.radio("Show", ["🟢 + 🟡 best matches", "All"], horizontal=True, key="sw_lv")
    show = [c for c in cands if lv == "All" or c["level"] != "possible"] or cands
    st.dataframe(pd.DataFrame([{
        "Match": SWAP_LEVEL_LABEL[c["level"]], "Colleague": c["partner_name"],
        "Designation": DESIG_FULL.get(c["partner_desig"], c["partner_desig"]),
        "You would take": _duty_txt(c["date"], c["session"]),
        "They would take": _duty_txt(my_alloc["duty_date"], my_alloc["session"]),
    } for c in show]), use_container_width=True, hide_index=True)

    ci = st.selectbox("Send request to", range(len(show)),
                      format_func=lambda i: f"{SWAP_LEVEL_LABEL[show[i]['level']][:1]} "
                                            f"{show[i]['partner_name']} — take "
                                            f"{_duty_txt(show[i]['date'], show[i]['session'])}",
                      key="sw_cand_pick")
    st.caption("💡 Submit only after you and your colleague have agreed. The request goes "
               "straight to the Examination Committee; your colleague can see it on their page.")
    if st.button("📨 Submit Swap for Approval", type="primary", use_container_width=True,
                 key="sw_send", disabled=preview):
        c = show[ci]
        db_swap_create({
            "requester_id": me, "requester_name": people[me]["name"],
            "req_alloc_id": str(my_alloc["id"]), "req_date": str(_alloc_date(my_alloc)),
            "req_session": str(my_alloc["session"]).upper(),
            "partner_id": c["partner_id"], "partner_name": c["partner_name"],
            "partner_alloc_id": str(c["alloc"]["id"]), "partner_date": str(c["date"]),
            "partner_session": c["session"], "match_level": c["level"],
            "status": "pending_admin",
        })
        st.success(f"Swap with {c['partner_name']} submitted to the Examination Committee for approval.")
        st.rerun()


def admin_swap_panel(fac_df):
    st.markdown("### 🔄 Duty Swap Requests")
    try:
        swaps = db_swaps_all()
    except Exception:
        st.warning("The `duty_swaps` table does not exist yet. Run this once in Supabase → SQL Editor, "
                   "then reload:")
        st.code(SWAP_TABLE_SQL, language="sql")
        return
    pend = [s for s in swaps if s.get("status") == "pending_admin"]
    st.markdown(f"#### 🕒 Waiting for your approval ({len(pend)})")
    if not pend:
        st.caption("No swaps waiting for approval.")
    allocs = db_get_all_allocation() if pend else []
    people = _swap_people(fac_df) if pend else {}
    for sw in pend:
        err = validate_swap(sw, allocs, people)
        st.markdown(
            "<div style='background:#f8fafc;border:2px solid #94a3b8;border-radius:10px;"
            "padding:10px 14px;margin:6px 0'>"
            f"<b>Swap #{sw['id']}</b> &nbsp; {SWAP_LEVEL_LABEL.get(sw.get('match_level'), '')}<br>"
            f"<b>{sw['requester_name']}</b> ({sw['requester_id']}) → takes "
            f"<b>{_duty_txt(sw['partner_date'], sw['partner_session'])}</b><br>"
            f"<b>{sw['partner_name']}</b> ({sw['partner_id']}) → takes "
            f"<b>{_duty_txt(sw['req_date'], sw['req_session'])}</b><br>"
            + (f"<span style='color:#b91c1c'>⚠ {err}</span>" if err
               else "<span style='color:#15803d'>✔ Still valid — all rules checked</span>")
            + "</div>", unsafe_allow_html=True)
        c1, c2, c3 = st.columns([1, 1, 2])
        note = c3.text_input("Note (optional)", key=f"sw_note_{sw['id']}",
                             label_visibility="collapsed", placeholder="Note (optional)")
        if c1.button("✅ Approve", key=f"sw_ap_{sw['id']}", type="primary",
                     use_container_width=True, disabled=bool(err)):
            e2 = apply_swap(sw, fac_df)
            if e2:
                st.error(e2)
            else:
                if note:
                    db_swap_update(sw["id"], {"admin_note": note})
                st.success(f"Swap #{sw['id']} approved — both allotments updated.")
                st.rerun()
        if c2.button("⛔ Reject", key=f"sw_rj_{sw['id']}", use_container_width=True):
            db_swap_update(sw["id"], {"status": "rejected", "admin_decided_at": _now_iso(),
                                      "admin_note": note or err or ""})
            st.rerun()

    st.markdown("---")
    st.markdown("#### 📜 Swap Log")
    if not swaps:
        st.caption("No swap requests yet.")
    else:
        log = pd.DataFrame([{
            "Swap #": s["id"],
            "Requested on": str(s.get("created_at", ""))[:16].replace("T", " "),
            "Requester": f"{s['requester_name']} ({s['requester_id']})",
            "Requester gives": _duty_txt(s["req_date"], s["req_session"]),
            "Partner": f"{s['partner_name']} ({s['partner_id']})",
            "Partner gives": _duty_txt(s["partner_date"], s["partner_session"]),
            "Match": SWAP_LEVEL_LABEL.get(s.get("match_level"), ""),
            "Status": SWAP_STATUS_LABEL.get(s.get("status"), s.get("status")),
            "Note": s.get("admin_note") or "",
        } for s in swaps])
        st.dataframe(log, use_container_width=True, hide_index=True)
        _xb = io.BytesIO()
        with pd.ExcelWriter(_xb, engine="openpyxl") as _xw:
            log.to_excel(_xw, sheet_name="Swap Log", index=False)
            _al = pd.DataFrame(db_get_all_allocation())
            if not _al.empty:
                _al["Date"] = _al["duty_date"].apply(lambda d: _duty_txt(d, "")[:-1])
                _al = _al.rename(columns={"faculty_id": "ID No.", "faculty_name": "Name",
                                          "designation": "Designation", "session": "Session",
                                          "allocated_by": "Allocated By"})
                _cols = [c for c in ["ID No.", "Name", "Designation", "Date", "Session",
                                     "Allocated By"] if c in _al.columns]
                _al[_cols].to_excel(_xw, sheet_name="Current Allotment", index=False)
        st.download_button("⬇ Download Swap Log (Excel)", data=_xb.getvalue(),
                           file_name=f"Swap_Log_{datetime.date.today():%d-%m-%Y}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                           key="dl_swap_log")


def page_allotment(fac_df, sel_name, sel_clean, frow, offline_df, online_df):
    st.markdown("### My Allotment Details")

    _aslot_dates = set(offline_df["Date"].dt.date.dropna())
    _as, _ae     = get_exam_period(_aslot_dates)
    if _as and _ae:
        st.markdown(
            f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
            f"padding:10px 16px;margin-bottom:12px;font-size:.93rem;color:#0c4a6e'>"
            f"📅 <b>Exam Period:</b> "
            f"<b>{_as.strftime('%d-%m-%Y')} ({_as.strftime('%A')})</b>"
            f" → <b>{_ae.strftime('%d-%m-%Y')} ({_ae.strftime('%A')})</b>"
            f"</div>", unsafe_allow_html=True)

    if not gate_is_open():
        st.markdown(
            "<div style='background:#fef3c7;border:2px solid #f59e0b;border-radius:12px;"
            "padding:22px 26px;text-align:center;margin:18px 0'>"
            "<div style='font-size:2.2rem;margin-bottom:8px'>⏳</div>"
            "<div style='font-size:1.15rem;font-weight:700;color:#92400e'>"
            "Allotment results are being processed</div>"
            "<div style='font-size:.93rem;color:#78350f;margin-top:6px'>"
            "The Examination Committee is reviewing the final allocation. "
            "Please check back shortly.</div>"
            "</div>", unsafe_allow_html=True)
        return

    vd = [f"{fmt_day(d.strftime('%d-%m-%Y'))} - Full Day" for d in valuation_dates_for(frow, sel_name)]
    qd = [fmt_day(d) for d in qp_dates_for(frow)]

    wd2   = load_willingness()
    wdisp = []
    will_pairs: set = set()
    if not wd2.empty:
        wm = fac_mask(wd2, sel_clean); wr = wd2[wm]
        if not wr.empty and {"Date", "Session"}.issubset(wr.columns):
            for d2, s2 in zip(wr["Date"], wr["Session"]):
                nd = to_dt(d2)
                if pd.notna(nd):
                    wdisp.append(f"{fmt_day(d2)} - {str(s2).upper()}")
                    will_pairs.add((nd.date(), str(s2).upper()))

    _logged_fid_allot = (st.session_state.get("_preview_fid")
                         or st.session_state.get("_logged_fid", ""))
    _allot_db_rows    = db_get_allocation_for(_logged_fid_allot) if _logged_fid_allot else []
    idisp = []
    allot_pairs: set = set()
    for _arow in _allot_db_rows:
        _raw_d  = _arow.get("duty_date","")
        _sess   = str(_arow.get("session","")).strip().upper()
        _mode   = str(_arow.get("duty_type","")).strip()
        _sat_tag = ""
        try:
            if parse_date_safe(_raw_d).weekday() == 5:
                _sat_tag = " — Saturday"
        except: pass
        idisp.append(f"{fmt_day(_raw_d)} - {_sess} ({_mode}){_sat_tag}")
        nd2 = parse_date_safe(_raw_d)
        if pd.notna(nd2):
            allot_pairs.add((nd2.date(), _sess))

    if will_pairs:
        matched = len(will_pairs & allot_pairs)
        acc_pct = f"{matched/len(will_pairs)*100:.1f}%  ({matched}/{len(will_pairs)})"
    else:
        acc_pct = "Not available"

    c1, c2 = st.columns(2)
    with c1:
        st.markdown('<div class="panel"><div class="sec-title">📝 Willingness Submitted</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date & Session": wdisp or ["Not submitted"]}),
                     use_container_width=True, hide_index=True)
        st.markdown('<div class="panel"><div class="sec-title">🏛️ IG Duty Allotment</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date, Session & Type": idisp or ["Not allotted yet"]}),
                     use_container_width=True, hide_index=True)
    with c2:
        st.markdown('<div class="panel"><div class="sec-title">📋 Valuation Dates</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date": vd or ["Not available"]}),
                     use_container_width=True, hide_index=True)
        st.markdown('<div class="panel"><div class="sec-title">💬 QP Feedback Dates</div></div>',
                    unsafe_allow_html=True)
        st.dataframe(pd.DataFrame({"Date": qd or ["Not available"]}),
                     use_container_width=True, hide_index=True)

    st.markdown(
        f"<div style='margin-top:10px;padding:12px 16px;background:#f0fdf4;"
        f"border:1.5px solid #86efac;border-radius:10px;font-size:.9rem;color:#166534'>"
        f"📊 <b>Willingness Accommodation:</b> {acc_pct}</div>",
        unsafe_allow_html=True)

    if _allot_db_rows:
        section_swap(fac_df, _logged_fid_allot,
                     preview=bool(st.session_state.get("_preview_fid")))

    st.markdown(
        "<div style='margin-top:10px;padding:10px 14px;background:#f1f5f9;"
        "border-radius:8px;border:1px solid #cbd5e1;font-size:.82rem;color:#475569'>"
        "📩 For support or clarification, contact the "
        "<strong>University Examination Committee, SoME</strong>.</div>",
        unsafe_allow_html=True)

    msg = build_msg(sel_name, wdisp, vd, idisp, qd)
    st.markdown('<div class="panel"><div class="sec-title">📲 Share via WhatsApp</div></div>',
                unsafe_allow_html=True)
    st.markdown("**Message Preview:**")
    st.code(msg, language="text")
    wph = st.text_input("WhatsApp Number (with country code)", placeholder="+919876543210")
    if wph.strip():
        lnk = wa_link(wph.strip(), msg)
        st.markdown(
            f'<a href="{lnk}" target="_blank" style="display:inline-block;'
            f'background:#25D366;color:white;padding:10px 22px;border-radius:10px;'
            f'font-weight:700;text-decoration:none;margin-top:6px">'
            f'📲 Open WhatsApp &amp; Send</a>', unsafe_allow_html=True)
    else:
        st.caption("Enter your WhatsApp number above to generate the send link.")


# ═══════════════════════════════════════════════════════════════ #
#             WILLINGNESS SUBMISSION PAGE                        #
# ═══════════════════════════════════════════════════════════════ #
def page_willingness(fac_df, offline_df, online_df, sel_name, frow):
    sel_clean = clean(sel_name)
    desig2    = str(frow["Designation"]).strip().upper()
    val_d2    = valuation_dates_for(frow, sel_name)
    val_s2    = set(val_d2)
    fn_clean  = _norm_name(sel_name)
    min_d, _  = fac_duty_range(sel_name, desig2)
    if fn_clean in FACULTY_WILL_OVERRIDE:
        req_cnt = FACULTY_WILL_OVERRIDE[fn_clean]
    elif fn_clean in FIVE_DUTY_CLEAN:
        req_cnt = 12    # 4 specific TA: 5 duties → 12 willingness options
    elif fn_clean in SAT_PREASSIGN_CLEAN:
        req_cnt = 11    # First 13 TA + RA: 4 duties → 11 willingness options
    else:
        req_cnt = DUTY_STRUCTURE.get(desig2, 0)

    if req_cnt == 0:
        st.warning(f"Designation '{desig2}' not recognised. Contact admin.")
        return

    # All designations use offline slots this semester
    sopts = offline_df.copy()
    sopts["Date"]     = pd.to_datetime(sopts["Date"], errors="coerce")
    sopts["DateOnly"] = sopts["Date"].dt.date
    fac_blackout_dates = FACULTY_BLACKOUT_CLEAN.get(_exam_key(sel_name), set())
    fac_exam_dates     = FACULTY_EXAM_DATES_CLEAN.get(_exam_key(sel_name), set())
    fac_lab_dates      = FACULTY_LAB_DATES_CLEAN.get(_exam_key(sel_name), set())

    # Saturdays are open to all designations this semester (optional)
    _sat_blocked_desig = False

    # Saturday dates in the slot list — used for calendar highlight + selector filter
    _all_sat_dates = {d for d in sopts["DateOnly"].dropna().unique() if d.weekday() == 5}

    valid_d = sorted([
        d for d in sopts["DateOnly"].dropna().unique()
        if d not in val_s2
        and d not in fac_blackout_dates
        and not (_sat_blocked_desig and d.weekday() == 5)
    ])

    if st.session_state.selected_faculty != sel_clean:
        st.session_state.selected_faculty = sel_clean
        st.session_state.selected_slots   = []
        st.session_state["picked_date"]   = valid_d[0] if valid_d else None

    if st.session_state.get("picked_date") not in valid_d:
        # stale value (e.g. page opened before slots were loaded) → reset
        st.session_state["picked_date"] = valid_d[0] if valid_d else None

    # Show exam period banner
    _slot_dates_user = set(offline_df["Date"].dt.date.dropna())
    _exam_start, _exam_end = get_exam_period(_slot_dates_user)

    _period_str = ""
    if _exam_start and _exam_end:
        _period_str = (
            f"📅 <b>Exam Period:</b> "
            f"<b>{_exam_start.strftime('%d-%m-%Y')} ({_exam_start.strftime('%A')})</b>"
            f" → <b>{_exam_end.strftime('%d-%m-%Y')} ({_exam_end.strftime('%A')})</b>")

    st.markdown(
        f"<div style='background:#e0f2fe;border:1.5px solid #38bdf8;border-radius:10px;"
        f"padding:10px 16px;margin-bottom:4px;font-size:.93rem;color:#0c4a6e'>"
        f"{_period_str}</div>", unsafe_allow_html=True)

    left, right = st.columns([1, 1.4])

    with left:
        st.subheader("Willingness Submission")

        st.write(f"**Designation:** {DESIG_FULL.get(desig2, desig2)}")
        if desig2 not in DESIG_RULES:
            st.error(f"⚠️ Designation code '{desig2}' not recognised. "
                     f"Raw value in DB: '{frow.get('designation', '?')}'. Contact admin.")
            return
        # Duty count: check explicit lists first, then DESIG_RULES
        _duties_count = fac_duty_range(sel_name, desig2)[0]
        duties_label = str(_duties_count)
        st.write(f"**Duties to be Allotted:** {duties_label}")
        st.write(f"**Options to Select:** {req_cnt}")

        # Lab examination duty notice
        if fac_lab_dates:
            _lab_list = " &nbsp;·&nbsp; ".join(
                f"<b>{d.strftime('%d-%m-%Y (%A)')}</b>" for d in sorted(fac_lab_dates))
            st.markdown(f"""
<div style="background:#f5f3ff;border:2px solid #8b5cf6;border-radius:12px;
            padding:12px 16px;margin:8px 0 12px 0">
  <div style="font-size:.93rem;font-weight:800;color:#5b21b6">
    🧪 Lab Examination Duty — Dates Locked
  </div>
  <div style="font-size:.84rem;color:#4c1d95;margin-top:5px">
    You are an examiner for the MEC103 Engineering Practices Laboratory examination on: {_lab_list}
  </div>
  <div style="font-size:.78rem;color:#6d28d9;margin-top:6px;border-top:1px solid #ddd6fe;padding-top:5px">
    These dates are excluded from willingness selection and End-Semester duty allotment.
  </div>
</div>""", unsafe_allow_html=True)

        # Exam date notice (only for faculty with exam dates)
        if fac_exam_dates:
            _exam_rows = "".join(
                f"<li style='margin:3px 0'><b>{d.strftime('%d-%m-%Y (%A)')}</b></li>"
                for d in sorted(fac_exam_dates)
            )
            _buf_dates = fac_blackout_dates - fac_exam_dates - fac_lab_dates
            _buf_rows  = "".join(
                f"<li style='margin:3px 0'>{d.strftime('%d-%m-%Y (%A)')} (buffer)</li>"
                for d in sorted(_buf_dates)
            )
            _buf_note  = (
                f"<div style='font-size:.78rem;color:#b45309;margin-top:4px'>"
                f"📌 Buffer (n−1, n−2 working days before exam) also locked — "
                f"no duty will be assigned: "
                + ", ".join(d.strftime("%d-%m-%Y") for d in sorted(_buf_dates))
                + "</div>"
            ) if _buf_dates else ""
            st.markdown(f"""
<div style="background:#fee2e2;border:2px solid #ef4444;border-radius:12px;
            padding:12px 16px;margin:8px 0 12px 0">
  <div style="font-size:.93rem;font-weight:800;color:#991b1b">
    🚫 Exam Dates — Locked (cannot be selected)
  </div>
  <ul style="font-size:.87rem;color:#7f1d1d;margin:6px 0 2px 16px;padding:0">
    {_exam_rows}
  </ul>
  {_buf_note}
  <div style="font-size:.78rem;color:#b91c1c;margin-top:6px;border-top:1px solid #fca5a5;padding-top:5px">
    ⚠️ You have exams on the above dates. These and their buffer days are excluded from selection and allotment.
  </div>
</div>""", unsafe_allow_html=True)

        # Saturday duty notice — open to all designations (shown to everyone)
        _sat_list = (" &nbsp;·&nbsp; ".join(
            f"<b>{d.strftime('%d-%m-%Y')}</b>" for d in sorted(_all_sat_dates))
            if _all_sat_dates else "will be shown once the examination schedule is published")
        _sat_rule = (
            "As per the usual practice, TA/RA members may be allotted Saturday duties."
            if desig2 in SAT_ALWAYS_DESIG else
            "Saturday duty will be allotted <b>only</b> to faculty members who include "
            "the respective Saturday in their willingness."
        )
        st.markdown(f"""
<div style="background:#eff6ff;border:2px solid #60a5fa;border-radius:12px;
            padding:12px 16px;margin:8px 0 12px 0">
  <div style="font-size:.93rem;font-weight:800;color:#1e3a8a">
    📢 Notice: Saturday Examination Duty
  </div>
  <div style="font-size:.84rem;color:#1e40af;margin-top:6px;line-height:1.5">
    For the Odd Semester 2026-27 End-Semester Examinations, Saturday duties are
    <b>open to faculty members of all designations</b>. Interested faculty members
    may kindly include Saturday(s) in their willingness options.
  </div>
  <div style="font-size:.82rem;color:#1e3a8a;margin-top:6px">{_sat_rule}</div>
  <div style="font-size:.8rem;color:#475569;margin-top:6px;
              border-top:1px solid #bfdbfe;padding-top:6px">
    Saturday examination dates: {_sat_list}
  </div>
</div>""", unsafe_allow_html=True)

        st.markdown("""
<div style="background:#f0f7ff;border:1.5px solid #93c5fd;border-radius:12px;
            padding:14px 16px;margin:8px 0 14px 0">
  <div style="font-size:.88rem;font-weight:800;color:#1e3a5f;margin-bottom:8px">
    ℹ️ How Your Duty Will Be Allotted
  </div>
  <table style="width:100%;margin-top:8px;border-collapse:collapse;font-size:.81rem">
    <tr>
      <td style="padding:4px 8px;width:28px">✅</td>
      <td style="padding:4px 6px;font-weight:700;color:#065f46;width:180px">Exact Match</td>
      <td style="padding:4px 6px;color:#374151">Allotted on the exact date &amp; session you submit</td>
    </tr>
    <tr style="background:#f8fafc">
      <td style="padding:4px 8px">🔄</td>
      <td style="padding:4px 6px;font-weight:700;color:#92400e">Session Adjusted</td>
      <td style="padding:4px 6px;color:#374151">Same date, FN↔AN swapped if needed</td>
    </tr>
    <tr>
      <td style="padding:4px 8px">📅</td>
      <td style="padding:4px 6px;font-weight:700;color:#9a3412">Date Adjusted</td>
      <td style="padding:4px 6px;color:#374151">Shifted ±1 working day from your submitted date</td>
    </tr>
    <tr style="background:#f8fafc">
      <td style="padding:4px 8px">🗓️</td>
      <td style="padding:4px 6px;font-weight:700;color:#5b21b6">Valuation-Adjacent</td>
      <td style="padding:4px 6px;color:#374151">Day before/after your valuation date</td>
    </tr>
    <tr>
      <td style="padding:4px 8px">🔴</td>
      <td style="padding:4px 6px;font-weight:700;color:#991b1b">System-Assigned</td>
      <td style="padding:4px 6px;color:#374151">No match — assigned to meet slot requirements</td>
    </tr>
  </table>
  <div style="font-size:.78rem;color:#64748b;margin-top:10px;border-top:1px solid #bfdbfe;padding-top:8px">
    💡 Submit dates spread across the exam period to maximise your match rate.
    Valuation dates are automatically protected.
  </div>
</div>""", unsafe_allow_html=True)

        if not valid_d:
            st.warning("No dates available for selection.")
        else:
            picked = st.selectbox(
                "Choose Offline Date",
                valid_d, key="picked_date",
                format_func=lambda d: d.strftime("%d-%m-%Y (%A)"))
            avail = set(sopts[sopts["DateOnly"] == picked]["Session"]
                        .dropna().astype(str).str.upper())

            all_will_now   = get_all_willingness()
            any_prob_shown = False
            for sess_opt in ["FN", "AN"]:
                if sess_opt in avail:
                    prob_info = slot_probability(all_will_now, sopts, picked, sess_opt)
                    if prob_info["seats"] > 0:
                        render_prob_bar(prob_info, sess_opt)
                        any_prob_shown = True
            if any_prob_shown:
                st.caption("⚡ Probability = available seats ÷ total applicants for that session.")

            b1, b2 = st.columns(2)
            with b1:
                add_fn = st.button(
                    "➕ Add FN", use_container_width=True,
                    disabled=("FN" not in avail or
                              len(st.session_state.selected_slots) >= req_cnt))
            with b2:
                add_an = st.button(
                    "➕ Add AN", use_container_width=True,
                    disabled=("AN" not in avail or
                              len(st.session_state.selected_slots) >= req_cnt))

            def add_slot(sess):
                exist = {s["Date"] for s in st.session_state.selected_slots}
                sl2   = {"Date": picked, "Session": sess}
                if picked in val_s2:
                    st.warning("Valuation date — cannot select.")
                elif picked in exist:
                    st.warning("Both FN and AN on same date not allowed.")
                elif len(st.session_state.selected_slots) >= req_cnt:
                    st.warning("Count reached.")
                elif sl2 in st.session_state.selected_slots:
                    st.warning("Already selected.")
                else:
                    st.session_state.selected_slots.append(sl2)

            if add_fn: add_slot("FN")
            if add_an: add_slot("AN")

        st.session_state.selected_slots = st.session_state.selected_slots[:req_cnt]
        st.write(f"**Selected:** {len(st.session_state.selected_slots)} / {req_cnt}")

        sdf = pd.DataFrame(st.session_state.selected_slots)
        if not sdf.empty:
            sdf = sdf.sort_values(["Date", "Session"]).reset_index(drop=True)
            sdf.insert(0, "Sl.No", sdf.index + 1)
            sdf["Day"]  = pd.to_datetime(sdf["Date"]).dt.day_name()
            sdf["Date"] = pd.to_datetime(sdf["Date"]).dt.strftime("%d-%m-%Y")
            st.dataframe(sdf[["Sl.No", "Date", "Day", "Session"]],
                         use_container_width=True, hide_index=True)
            rm = st.selectbox("Sl.No to remove", options=sdf["Sl.No"].tolist())
            if st.button("🗑 Remove Row", use_container_width=True):
                tgt = sdf[sdf["Sl.No"] == rm].iloc[0]
                td  = to_dt(tgt["Date"]).date()
                ts  = tgt["Session"]
                st.session_state.selected_slots = [
                    s for s in st.session_state.selected_slots
                    if not (s["Date"] == td and s["Session"] == ts)]
                st.rerun()

        is_already = already_submitted(sel_name)
        st.markdown("### Submit Willingness")
        rem2 = max(req_cnt - len(st.session_state.selected_slots), 0)

        if is_already:
            st.warning("⚠ You have already submitted. Submitting again will **replace** your previous choices.")
        if rem2 == 0 and req_cnt > 0:
            st.success(f"✅ All {req_cnt} options selected. Ready to submit.")
        elif not is_already:
            st.info(f"Select {rem2} more option(s) to enable submission.")

        _preview = bool(st.session_state.get("_preview_fid"))
        if _preview:
            st.info("👁 Admin preview — submission is disabled here.")
        if st.button("✅ Submit Willingness",
                     disabled=(_preview or len(st.session_state.selected_slots) != req_cnt),
                     use_container_width=True):
            save_submission(sel_name, st.session_state.selected_slots)
            st.session_state.selected_slots = []
            action = "re-submitted" if is_already else "submitted"
            st.toast(f"Willingness {action} successfully! ✅", icon="✅")
            st.success(
                "Thank you for submitting. The final duty allocation will be carried out "
                "using MILP optimization. Check this portal for allotment updates.")

    with right:
        # All designations see the Offline Duty Calendar this semester
        render_calendar(offline_df, val_s2, "Offline Duty Calendar",
                        exam_dates=fac_exam_dates,
                        buffer_dates=(fac_blackout_dates - fac_exam_dates - fac_lab_dates),
                        lab_dates=fac_lab_dates,
                        sat_blocked_dates=(_all_sat_dates if _sat_blocked_desig else set()))


# ═══════════════════════════════════════════════════════════════ #
#                         MAIN ROUTER                            #
# ═══════════════════════════════════════════════════════════════ #
def main():
    # ── 1. Load faculty + slots from Supabase ────────────────────
    @st.cache_data(ttl=300)
    def _load_fac():
        rows = db_get_all_faculty()
        if not rows:
            st.error("No faculty found in Supabase. Run load_to_supabase.py first.")
            st.stop()
        df = pd.DataFrame(rows)
        df["ID No."]      = df["faculty_id"].astype(str).apply(_norm_id)
        df["Name"]        = df["name"].astype(str).str.strip()
        df["NAME OF STAFF"] = df["Name"]
        df["Designation"] = df["designation"].astype(str).apply(_map_desig)
        # Apply per-faculty overrides (handles NULL/blank Supabase values)
        for _i, _r in df.iterrows():
            _fc = _norm_name(_r["Name"])
            if _fc in FACULTY_DESIG_OVERRIDE:
                df.at[_i, "Designation"] = FACULTY_DESIG_OVERRIDE[_fc]
        df["Clean"]       = df["Name"].apply(clean)
        for col in ["v1","v2","v3","v4","v5"]:
            cap = col.upper()
            df[cap] = to_dt(df[col]) if col in df.columns else pd.NaT
        return df

    fac_df = _load_fac()
    offline_df, online_df = load_slots(OFFLINE_FILE, ONLINE_FILE)

    # ── 2. Login gate ─────────────────────────────────────────────
    if not st.session_state.logged_in:
        page_login(fac_df)
        return

    # ── 3. Force password change ──────────────────────────────────
    if st.session_state.must_change_pw:
        page_force_change_password()
        return

    # ── 4. Header + notice banner ─────────────────────────────────
    render_header(logo=False)
    st.markdown(
        "<div class='blink'><strong>Note:</strong> The University Examination Committee "
        "sincerely appreciates your cooperation. Every effort will be made to accommodate "
        "your willingness. Final duty allocation is carried out using AI-assisted MILP "
        "optimization.</div>", unsafe_allow_html=True)
    st.markdown("")

    # ── 5. Welcome row + logout ───────────────────────────────────
    col_title, col_logout = st.columns([6, 1])
    with col_logout:
        if st.button("🚪 Logout"):
            for k in ["logged_in", "faculty_id", "faculty_name", "faculty_clean",
                      "is_admin", "must_change_pw", "selected_slots", "selected_faculty"]:
                st.session_state[k] = (
                    [] if k == "selected_slots"
                    else (False if k not in ("faculty_id", "faculty_name", "faculty_clean") else ""))
            st.rerun()
    with col_title:
        fid_disp  = st.session_state.faculty_id
        name_disp = st.session_state.faculty_name
        is_admin  = st.session_state.is_admin
        badge     = " 👑 Admin" if is_admin else ""
        st.markdown(
            f"**Welcome, {name_disp}** &nbsp; <span style='color:#64748b;font-size:.88rem'>"
            f"({fid_disp})</span>{badge}",
            unsafe_allow_html=True)

    # ── 6. Main panel routing ─────────────────────────────────────
    if is_admin:
        menu = st.radio("Main Menu", ["User View", "Admin View", "👁 View as Faculty"],
                        horizontal=True, key="panel_mode")
        st.session_state["_preview_fid"] = ""
        if menu == "👁 View as Faculty":
            _all = db_get_all_faculty()
            _opts = {f'{r["name"]} ({r["faculty_id"]})': r for r in
                     sorted(_all, key=lambda r: str(r.get("name", "")).lower())}
            _pick = st.selectbox("Select faculty to see exactly what they see", list(_opts),
                                 key="preview_fac_pick")
            _r = _opts[_pick]
            _pname  = str(_r["name"]).strip()
            _pmatch = fac_df[fac_df["Clean"] == clean(_pname)]
            st.markdown(
                "<div style='background:#fef9c3;border:2px solid #eab308;border-radius:10px;"
                "padding:8px 14px;margin:6px 0 10px 0;font-weight:700;color:#713f12'>"
                f"👁 Admin preview — viewing the portal as <u>{_pname}</u> "
                f"({_r['faculty_id']}). Nothing can be submitted from here.</div>",
                unsafe_allow_html=True)
            if _pmatch.empty:
                st.error("This faculty's record was not found in the loaded faculty list — "
                         "this is exactly the error they would see. Click 'Clear All Cached Data' "
                         "in Admin View and check their name/designation in Supabase.")
            else:
                st.session_state["_preview_fid"] = _norm_id(_r["faculty_id"])
                _prow = _pmatch.iloc[0]
                st.caption(f"Designation in portal: **{_prow['Designation']}** · "
                           f"Raw in Supabase: **{_r.get('designation', '')}**")
                _ptab = st.radio("Their view", ["Willingness", "My Allotment"],
                                 horizontal=True, key="preview_tab")
                if _ptab == "Willingness":
                    page_willingness(fac_df, offline_df, online_df, _pname, _prow)
                else:
                    page_allotment(fac_df, _pname, clean(_pname), _prow, offline_df, online_df)
            st.markdown("---")
            st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
            return
        if menu == "Admin View":
            page_admin(fac_df, offline_df, online_df)
            st.markdown("---")
            st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")
            return

    # ── 7. User view panel ────────────────────────────────────────
    sub = st.radio("View", ["Willingness", "My Allotment", "Change Password"],
                   horizontal=True, key="user_panel_mode")

    sel_name  = st.session_state.faculty_name
    sel_clean = st.session_state.faculty_clean
    fmatch    = fac_df[fac_df["Clean"] == sel_clean]

    if fmatch.empty:
        st.error("Your faculty record was not found. Contact admin.")
        st.stop()

    frow = fmatch.iloc[0]

    if sub == "My Allotment":
        page_allotment(fac_df, sel_name, sel_clean, frow, offline_df, online_df)
    elif sub == "Change Password":
        section_change_password()
    else:
        page_willingness(fac_df, offline_df, online_df, sel_name, frow)

    st.markdown("---")
    st.caption("Curated by Dr. N. Sathiya Narayanan | School of Mechanical Engineering")


main()
