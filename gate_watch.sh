#!/bin/bash
# gate_watch.sh — daily Heilbronn-triangle gate poll (R2125607854, probe report
# gate-watch section). Prints ONE status line. Exit codes: 0 = gate closed,
# 2 = GATE OPEN (heilbronn profile exists — file Stage A within hours),
# 1 = poll error (network/gh). Cheap: 3 read-only gh api calls.
# Usage: ./gate_watch.sh   (cron/launchd daily, or by hand)
set -uo pipefail
REPO="bigospeedrun/verifier"
TS="$(date -u +%Y-%m-%dT%H:%MZ)"

# 1. profiles/ listing — the authoritative gate signal
profiles="$(gh api "repos/$REPO/contents/profiles" --jq '.[].name' 2>/dev/null)" || {
  echo "[$TS] gate=POLL-ERROR profiles listing fetch failed"; exit 1; }
heil_profiles="$(printf '%s\n' "$profiles" | grep -i heilbronn || true)"

# 2. recent commits mentioning heilbronn (7-day window)
since="$(date -u -v-7d +%Y-%m-%dT%H:%M:%S 2>/dev/null || date -u -d '7 days ago' +%Y-%m-%dT%H:%M:%S)"
heil_commits="$(gh api "repos/$REPO/commits?since=$since&per_page=100" \
  --jq '[.[] | select(.commit.message | test("heilbronn"; "i"))] | length' 2>/dev/null || echo "?")"

# 3. open issues mentioning heilbronn (issue-form / submission route activity)
issues="$(gh api "search/issues?q=repo:$REPO+heilbronn+in:title,body&per_page=5" \
  --jq '.total_count' 2>/dev/null || echo "?")"

if [ -n "$heil_profiles" ]; then
  echo "[$TS] gate=OPEN PROFILE=$(printf '%s' "$heil_profiles" | tr '\n' ' ') commits7d=$heil_commits issues=$issues — FILE STAGE A NOW (stagea/ is green: Race.bound : Bound 0, axioms clean)"
  exit 2
fi
echo "[$TS] gate=CLOSED profiles=$(printf '%s\n' "$profiles" | wc -l | tr -d ' ')/heilbronn=0 commits7d(heilbronn)=$heil_commits issues(heilbronn)=$issues"
exit 0
