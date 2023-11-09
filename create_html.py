import os

PROJECT_NAME = "NMDSProofs"

# Get path to all Lean files
for file in os.listdir(PROJECT_NAME):
    if file.endswith(".lean"):
        lean_file = os.path.join(PROJECT_NAME, file)
        # Call Alectryon on each Lean file
        os.system(
            f"alectryon --frontend lean4 {lean_file} --lake lakefile.lean --webpage-style windowed --output-directory html"
        )
