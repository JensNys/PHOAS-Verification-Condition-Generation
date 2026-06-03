import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# 1. Load data
file_path = 'results.xlsx'
df = pd.read_excel(file_path, index_col=0)

# Ensure the X-axis (index) is numeric
df.index = pd.to_numeric(df.index, errors='coerce')
x_vals = df.index.tolist()


def finalize_plot(title, use_loglog=False):
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


# --- vcgen columns (vcgenreader_reader to vcgen_close/db) ---
all_cols = df.columns.tolist()
start_col = "vcgenreader_reader"
end_col = "vcgen_close/db"
vcgen_cols = all_cols[all_cols.index(start_col):all_cols.index(end_col) + 1]

if vcgen_cols:
    plt.figure(figsize=(10, 6))
    for col in vcgen_cols:
        plt.plot(x_vals, df[col], marker='o', label=col)
    finalize_plot('vcgen', use_loglog=False)
else:
    print("No vcgen columns found in the dataset.")