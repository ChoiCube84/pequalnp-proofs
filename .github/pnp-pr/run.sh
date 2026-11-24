#!/usr/bin/env bash
set -euo pipefail
export GH_PROMPT_DISABLED=1

owner=ChoiCube84
fork=$owner/pequalnp-proofs
upstream=open-goat/pequalnp-proofs
linkedin='**LinkedIn profile**: https://www.linkedin.com/in/jwchoi84'
mode=${1:?expected validate or submit}
request=${2:?expected a request JSON file}

fail() {
  printf '%s\n' "$*" >&2
  exit 1
}

operation=$(jq -er '.operation | strings' "$request")
case "$operation" in
  preflight|edit-linkedin)
    jq -e 'keys == ["operation"]' "$request" >/dev/null
    ;;
  create)
    jq -e 'keys == ["branch", "head_sha", "operation"]' "$request" >/dev/null
    branch=$(jq -er '.branch | strings' "$request")
    head_sha=$(jq -er '.head_sha | strings' "$request")
    [[ "$head_sha" =~ ^[0-9a-f]{40}$ ]] || fail 'Invalid proof commit SHA.'
    if [[ "$branch" =~ ^L-([a-z]+)-([0-9]+)$ ]]; then
      gap=$branch
      proof_path="lean/PEqualNP/Outside/L_${BASH_REMATCH[1]}_${BASH_REMATCH[2]}.lean"
      reduction=false
    elif [[ "$branch" =~ ^R-([a-z]+)-([0-9]+)-([1-9][0-9]{0,2})$ ]]; then
      gap="L-${BASH_REMATCH[1]}-${BASH_REMATCH[2]}"
      proof_path="lean/PEqualNP/Outside/R_${BASH_REMATCH[1]}_${BASH_REMATCH[2]}_${BASH_REMATCH[3]}.lean"
      reduction=true
    else
      fail 'Expected a project proof or reduction branch.'
    fi
    ;;
  *) fail 'Unknown operation.' ;;
esac

if [[ "$mode" == validate ]]; then
  gh --version
  [[ "$(gh api "repos/$fork" --jq .full_name)" == "$fork" ]] || fail 'Cannot read the fork.'
  printf 'operation=%s\n' "$operation" >> "${GITHUB_OUTPUT:?}"
  printf 'GitHub runner can read the fork. Requested operation: %s\n' "$operation"
  exit 0
fi
[[ "$mode" == submit && "$operation" != preflight ]] || fail 'Unsupported submission mode.'
[[ -n "${GH_TOKEN:-}" ]] || fail 'Configure PNP_GITHUB_TOKEN as an environment secret in codex-prs.'
[[ "$(gh api user --jq .login)" == "$owner" ]] || fail 'GitHub did not authenticate the expected PR author.'

temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT

if [[ "$operation" == edit-linkedin ]]; then
  route="repos/$upstream/pulls/9071"
  gh api "$route" > "$temp/before.json"
  python3 - "$temp" "$owner" "$linkedin" <<'PY'
import json
from pathlib import Path
import re
import sys

directory, owner, linkedin = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
pull = json.loads((directory / "before.json").read_text())
if pull["user"]["login"] != owner or pull["number"] != 9071:
    raise SystemExit("Unexpected PR author or number.")
body = pull["body"]
updated, count = re.subn(
    r"^\*\*LinkedIn profile\*\*[^\r\n]*", lambda _: linkedin, body, flags=re.M
)
if count != 1:
    raise SystemExit("Expected exactly one LinkedIn line.")
(directory / "patch.json").write_text(json.dumps({"body": updated}))
if updated != body:
    (directory / "changed").touch()
PY
  if [[ -f "$temp/changed" ]]; then
    gh api --method PATCH "$route" --input "$temp/patch.json" >/dev/null
  fi
  gh api "$route" | jq -er --slurpfile patch "$temp/patch.json" \
    'select(.body == $patch[0].body) | .html_url'
  exit 0
fi

route="repos/$upstream/pulls"
find_existing() {
  gh api --method GET "$route" -f state=all -f "head=$owner:$branch"
}

find_existing > "$temp/existing.json"
if jq -e 'length != 0' "$temp/existing.json" >/dev/null; then
  jq -er --arg sha "$head_sha" --arg owner "$owner" --arg body "$linkedin" \
    '.[] | select(.head.sha == $sha and .user.login == $owner and .body == $body) | .html_url' \
    "$temp/existing.json" || fail 'An existing PR uses this branch. Review it before retrying.'
  exit 0
fi

curl --proto '=https' --fail --silent --show-error --max-time 20 --max-filesize 12000000 \
  --get https://pequalnp.com/desk/step --data-urlencode "gap=$gap" > "$temp/step.json"
jq -e '.state == "leased"' "$temp/step.json" >/dev/null || fail 'The desk no longer reports an active lease.'
curl --proto '=https' --fail --silent --show-error --max-time 20 --max-filesize 12000000 \
  https://data.pequalnp.com/data/desk/gaps.json > "$temp/gaps.json"
jq -e --arg gap "$gap" --argjson reduction "$reduction" '
  any(.gaps[]; .id == $gap and (.pr_open // 0) == 0
    and ($reduction == false or .reductions == true))
' "$temp/gaps.json" >/dev/null || fail 'The desk no longer reports an eligible gap without a pending PR.'

gh api "repos/$upstream/compare/main...$owner:$branch" |
  jq -e --arg sha "$head_sha" --arg path "$proof_path" '
    .commits[-1].sha == $sha and (.files | length) == 1
    and .files[0].status == "added" and .files[0].filename == $path
  ' >/dev/null || fail 'The submitted branch must match the checked commit and add one proof file.'

jq -n --arg head "$owner:$branch" --arg title "$branch" --arg body "$linkedin" \
  '{head:$head,base:"main",title:$title,body:$body}' > "$temp/pull.json"
gh api --method POST "$route" --input "$temp/pull.json" |
  jq -er --arg sha "$head_sha" --arg owner "$owner" --arg body "$linkedin" \
    'select(.head.sha == $sha and .user.login == $owner and .body == $body) | .html_url'
