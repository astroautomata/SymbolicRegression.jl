"""Run with uv run --no-project --with pyyaml python scripts/test_check_bugs.py."""

from copy import deepcopy
from pathlib import Path
from tempfile import TemporaryDirectory

import yaml

import check_bugs as checker

with TemporaryDirectory() as directory:
    root = Path(directory)
    template = (checker.ROOT / "bugs/schema.yaml.example").read_text(encoding="utf-8")
    bug = yaml.safe_load(template)
    checker.ROOT = root
    (root / "bugs").mkdir()
    (root / "bugs/schema.yaml.example").write_text(template, encoding="utf-8")
    (root / "repro").mkdir()
    path = root / "bugs" / f"{bug['id']}.yaml"
    repro = root / "repro" / f"{bug['id']}.jl"
    repro.touch()
    (root / "registry.tsv").write_text(
        f"{bug['id']}\trefuted\tgeneral\t1\tsrc/Example.jl\tStatement\tPreconditions\n"
        "example-other\trefuted\tgeneral\t1\tsrc/Example.jl\tStatement\tPreconditions\n"
        "example-proven\tproven\tgeneral\t1\tsrc/Example.jl\tStatement\tPreconditions\n",
        encoding="utf-8",
    )
    refuted = checker.refuted_ids(root / "registry.tsv")

    def check(**changes):
        path.write_text(yaml.safe_dump(dict(bug, **changes)), encoding="utf-8")
        return checker.check(path, refuted)

    assert checker.main() == 1  # Refuted ids need a report; the template doesn't count.
    assert not check()
    assert checker.main() == 1  # example-other is still unreported.
    assert not check(covers=["example-other"])
    assert checker.main() == 0
    assert check(covers=["example-proven"])
    assert check(covers=["example-missing"])
    assert check(id="example-other")
    assert check(priority=[])
    assert check(lean={"property": "SymReg.Example.property"})
    for key in ("julia_version", "sr_commit", "de_version", "output"):
        invalid = deepcopy(bug["runtime"])
        del invalid[key]
        assert check(runtime=invalid), key
    assert check(runtime=dict(bug["runtime"], de_version=2))
    path.write_text(yaml.safe_dump(dict(bug, id="example-proven")), encoding="utf-8")
    proven_path = path.with_name("example-proven.yaml")
    path.rename(proven_path)
    (root / "repro/example-proven.jl").touch()
    assert any("refuted" in problem for problem in checker.check(proven_path, refuted))
    assert checker.main() == 1
    repro.unlink()
    repro.mkdir()
    assert any("missing repro/" in problem for problem in check())

print("BUG CHECKER TEST OK")
