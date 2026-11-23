"""Validate bugs/*.yaml against the report schema, registry.tsv and repro/."""

from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
PRIORITIES = ("P0", "P1", "P2", "P3")
KINDS = ("wrong-result", "wrong-exception", "missing-error", "crash", "hang", "documentation")
TEXT = ("title", "area", "summary", "likelihood", "reproducer", "expected", "promised_by", "cause")
MAY_BE_EMPTY = ("maybe_intended", "possible_fix")
RUNTIME = ("julia_version", "sr_commit", "de_version", "output")
LEAN = ("property", "theorem")


def refuted_ids(path: Path) -> set[str]:
    ids = set()
    with path.open(encoding="utf-8") as registry:
        for number, line in enumerate(registry, 1):
            cols = line.split("\t", 2)
            if len(cols) != 3 or not cols[0] or cols[1] not in ("todo", "stuck", "proven", "refuted"):
                raise ValueError(f"{path.name}:{number}: expected a registry.tsv row")
            if cols[1] == "refuted":
                ids.add(cols[0])
    return ids


def nonempty(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def check(path: Path, refuted: set[str]) -> list[str]:
    try:
        bug = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (yaml.YAMLError, UnicodeError) as err:
        return [f"{path.name}: invalid YAML: {err}"]
    if not isinstance(bug, dict):
        return [f"{path.name}: top level is not a mapping"]
    problems = []

    def need(condition: bool, message: str) -> None:
        if not condition:
            problems.append(f"{path.name}: {message}")

    def known_keys(mapping: dict, keys: tuple[str, ...], where: str = "") -> None:
        for key in mapping:
            need(key in keys, f"unknown key {where}{key!r}")

    def text_list(value: object, key: str) -> None:
        need(isinstance(value, list) and bool(value) and all(map(nonempty, value)),
             f"{key} must be a nonempty list of nonempty strings")

    known_keys(bug, TEXT + MAY_BE_EMPTY + ("id", "priority", "kind", "files", "functions",
                                          "runtime", "duplicates", "lean", "covers"))
    need(bug.get("id") == path.stem, "id must match the file name")
    need(path.stem in refuted, f"{path.stem!r} is not a refuted registry id")
    need((ROOT / "repro" / f"{path.stem}.jl").is_file(), f"missing repro/{path.stem}.jl")
    need(bug.get("priority") in PRIORITIES, f"priority must be one of {', '.join(PRIORITIES)}")
    need(bug.get("kind") in KINDS, f"kind must be one of {', '.join(KINDS)}")
    for key in TEXT:
        need(nonempty(bug.get(key)), f"{key} must be a nonempty string")
    for key in MAY_BE_EMPTY:
        need(isinstance(bug.get(key), str), f"{key} must be a string")
    for key in ("files", "functions"):
        text_list(bug.get(key), key)
    for section, keys in (("runtime", RUNTIME), ("lean", LEAN)):
        mapping = bug.get(section)
        if not isinstance(mapping, dict):
            need(False, f"{section} must be a mapping")
        else:
            known_keys(mapping, keys, f"{section}.")
            for key in keys:
                need(nonempty(mapping.get(key)), f"{section}.{key} must be a nonempty string")

    duplicates = bug.get("duplicates")
    if not isinstance(duplicates, dict):
        need(False, "duplicates must be a mapping")
    else:
        known_keys(duplicates, ("issues", "queries"), "duplicates.")
        text_list(duplicates.get("queries"), "duplicates.queries")
        issues = duplicates.get("issues")
        if not isinstance(issues, list):
            need(False, "duplicates.issues must be a list")
        else:
            for issue in issues:
                need(isinstance(issue, dict) and type(issue.get("number")) is int
                     and issue["number"] > 0 and issue.get("relation") in ("duplicate", "related")
                     and ("state" not in issue or nonempty(issue["state"])),
                     f"invalid duplicates.issues entry {issue!r}")
                if isinstance(issue, dict):
                    known_keys(issue, ("number", "relation", "state"), "duplicates.issues.")

    covers = bug.get("covers", [])
    if not isinstance(covers, list) or not all(map(nonempty, covers)):
        need(False, "covers must be a list of registry ids")
    else:
        need(len(covers) == len(set(covers)), "covers must not repeat ids")
        for covered in covers:
            need(covered != path.stem and covered in refuted,
                 f"covers entry {covered!r} must be another refuted registry id")
    return problems


def main() -> int:
    files = sorted((ROOT / "bugs").glob("*.yaml"))
    try:
        refuted = refuted_ids(ROOT / "registry.tsv")
    except (OSError, ValueError) as err:
        print(err)
        return 1
    problems = [problem for path in files for problem in check(path, refuted)]
    reported = {path.stem for path in files}
    for path in files:
        try:
            bug = yaml.safe_load(path.read_text(encoding="utf-8"))
        except (yaml.YAMLError, UnicodeError):
            continue  # check() already reported it
        covers = bug.get("covers") if isinstance(bug, dict) else None
        if isinstance(covers, list):
            reported.update(c for c in covers if isinstance(c, str))
    problems += [f"registry.tsv: refuted {id!r} has no bug report or covers entry"
                 for id in sorted(refuted - reported)]
    for problem in problems:
        print(problem)
    print(f"BUGS {len(files)} PROBLEMS {len(problems)}")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
