"""Typecheck the release interface and confirm that four mathematical changes fail."""

from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CASES = (
    ("three_input_centroids", "(1/3:ℝ)", "(1/2:ℝ)"),
    ("binary_generator_classification", "(fun i ↦ -l i)", "l"),
    ("individual_triples", "l=0 ∨", "l=1 ∨"),
    ("arithmetic_predictions_of_triples", "∧ v = ∑ i, w i • x i", "∧ v = 0"),
)


def check_lean(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def main() -> None:
    solution = (ROOT / "Solution.lean").read_text()
    with tempfile.TemporaryDirectory() as temporary:
        control = Path(temporary) / "Control.lean"
        control.write_text(solution)
        result = check_lean(control)
        if result.returncode:
            raise RuntimeError(f"The unmodified interface failed.\n{result.stdout}")
        print("PASS unmodified Solution")

        for name, old, new in CASES:
            start = solution.index(f"theorem {name} ")
            stop = solution.index(" := by", start)
            statement = solution[start:stop]
            if statement.count(old) != 1:
                raise ValueError(f"Expected one matching expression in {name}")
            mutated = statement.replace(old, new)
            control.write_text(solution[:start] + mutated + solution[stop:])
            result = check_lean(control)
            if result.returncode == 0:
                raise AssertionError(f"Accepted corrupted declaration {name}")
            # The mutation must fail on the affected proof after the changed statement.
            first_line = solution.count("\n", 0, stop) + 1
            end = solution.find("\n\n", stop)
            last_line = solution.count("\n", 0, end) + 1
            expected = any(f"Control.lean:{line}:" in result.stdout
                           for line in range(first_line, last_line + 1))
            if not expected or "error" not in result.stdout:
                raise RuntimeError(f"Unexpected failure for {name}.\n{result.stdout}")
            print(f"PASS rejected corrupted {name}")


if __name__ == "__main__":
    main()
