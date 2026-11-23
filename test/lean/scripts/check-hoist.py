#!/usr/bin/env python3
"""Flag nested monadic actions in the RHS of Lean's pure short-circuit operators.

Lean hoists (← e) out of its containing do statement, so e runs even when the
RHS should be skipped. Use <&&> or <||> with a separate action on each side.
Known defects go in hoist-baseline.txt; new and stale entries fail the check.
"""
import re
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / 'scripts' / 'hoist-baseline.txt'
code_only = runpy.run_path(str(Path(__file__).with_name('check-proof-escapes.py')))['code_only']
OPERATOR = re.compile(r'(?<!<)(?:&&|\|\|)(?!>)')
TOKEN = re.compile(r'<&&>|<\|\|>|&&|\|\||<-|:=|=>|<\||[\w\'!?]+|\S')
END_RHS = {'then', 'else', 'with', 'do', 'by', 'in', '=>', ':=', ';', '|', ',', '<|', '$'}


def hoist_lines(source: str) -> set[int]:
    code = code_only(source)
    found = set()
    for op in OPERATOR.finditer(code):
        start = code.rfind('\n', 0, op.start()) + 1
        prefix = code[start:op.start()]
        indent = len(prefix) - len(prefix.lstrip(' \t'))
        nested_do = [False]
        for i, match in enumerate(TOKEN.finditer(code, op.end())):
            token = match.group()
            if len(nested_do) == 1:
                if token in END_RHS or (op.group() == '&&' and token == '||'):
                    break
                line_start = code.rfind('\n', 0, match.start()) + 1
                if i and line_start > start and match.start() - line_start <= indent:
                    break
            if token in {'(', '[', '{', '⟨'}:
                nested_do.append(nested_do[-1])
            elif token in {')', ']', '}', '⟩'}:
                nested_do.pop()
                if not nested_do:
                    break
            elif token in {'do', 'by'}:
                nested_do[-1] = True
            elif token in {'←', '<-'} and not nested_do[-1]:
                found.add(code.count('\n', 0, op.start()) + 1)
                break
    return found


def self_test():
    for source in [
        'if directory.isNone && testing then pure (some (← temporaryDirectory))',
        'if a || b then pure (← f) else pure (← g)',
        'if ← (pure a <&&> (do pure (← f))) then pure ()',
        'pure ((a && b), (← f))',
        'let x := a && b\npure (← f)',
        '-- a && (← f)\n/- a || (← f) -/\n#check r#"a && (← f)"#',
    ]:
        assert hoist_lines(source) == set(), source
    for source in [
        'if a && (← f x) then pure ()',
        'if a || !(← f) then pure ()',
        'if cellConst (← g.read l) && cellConst (← g.read r) then pure ()',
        'if a && /- ignore this -/ (\n  ← f) then pure ()',
        'if a &&\n  get (← f) then pure ()',
    ]:
        assert hoist_lines(source) == {1}, source
    print('HOIST self-test OK')


def main() -> int:
    if sys.argv[1:] == ['--self-test']:
        self_test()
        return 0
    baseline = {line for line in BASELINE.read_text(encoding='utf-8').splitlines()
                if line.strip() and not line.startswith('#')}
    found = {}
    for path in sorted((ROOT / 'SymReg').rglob('*.lean')):
        source = path.read_text(encoding='utf-8')
        lines = source.split('\n')
        name = path.relative_to(ROOT).as_posix()
        for line in sorted(hoist_lines(source)):
            text = lines[line - 1].strip()
            found[f'{name}\t{text}'] = f'{name}:{line}: {text}'
    new = sorted(found.keys() - baseline)
    stale = sorted(baseline - found.keys())
    for entry in new:
        print('HOIST', found[entry])
    for entry in stale:
        print('HOIST-FIXED (remove from baseline)', entry.replace('\t', ': ', 1))
    print(f'HOIST {len(found)} known {len(baseline)} new {len(new)} stale {len(stale)}')
    return int(bool(new or stale))


if __name__ == '__main__':
    sys.exit(main())
