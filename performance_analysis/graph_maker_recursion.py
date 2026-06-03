import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# 1. Load data
file_path = 'results.xlsx'
df = pd.read_excel(file_path, index_col=0)

# Ensure the X-axis (index) is numeric
df.index = pd.to_numeric(df.index, errors='coerce')
x_vals = df.index.tolist()


def finalize_recursion_plot(title, use_loglog=False):
    """Specific formatting for recursion plots."""
    plt.xlabel('Scale (Input Size)')
    plt.ylabel('Execution Time / Value')
    plt.title(title)
    plt.legend(loc='upper left', bbox_to_anchor=(1.05, 1))
    plt.grid(True, which="both", ls="-", alpha=0.3)

    if use_loglog:
        plt.xscale('log')
        plt.yscale('log')

    plt.tight_layout()
    plt.show()


# --- Recursion Analysis: Linear vs Log-Log ---
recursion_cols = [c for c in df.columns if 'vcgen_recursion' in str(c)]

if recursion_cols:
    # 1. Linear Recursion Plot
    plt.figure(figsize=(10, 6))
    for col in recursion_cols:
        plt.plot(x_vals, df[col], marker='s', label=col)
    finalize_recursion_plot('Recursion Analysis (Linear Scale)', use_loglog=False)

    # 2. Log-Log Recursion Plot
    plt.figure(figsize=(10, 6))
    for col in recursion_cols:
        # Filter out zero/negative values for logarithmic scaling
        valid_mask = df[col] > 0
        plt.plot(np.array(x_vals)[valid_mask], df[col][valid_mask], marker='s', label=col)
    finalize_recursion_plot('Recursion Analysis (Log-Log Scale)', use_loglog=True)
else:
    print("No recursion columns found in the dataset.")