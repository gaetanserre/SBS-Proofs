import os

PROJECT_NAME = "SBSProofs"

lean_files = [
    os.path.join(dp, f)
    for dp, dn, filenames in os.walk(PROJECT_NAME)
    for f in filenames
    if os.path.splitext(f)[1] == ".lean"
]

os.system("lake build")

for lean_file in lean_files:
    # Call Alectryon on each Lean file
    os.system(
        f"alectryon --frontend lean4 {lean_file} --lake lakefile.toml --webpage-style windowed --output-directory html"
    )
