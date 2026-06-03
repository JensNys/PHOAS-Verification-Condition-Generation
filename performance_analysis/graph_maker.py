import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import os

# 1. Load data
file_path = 'results.xlsx'
df = pd.read_excel(file_path, index_col=0)

# Ensure the X-axis (index) is numeric
df.index = pd.to_numeric(df.index, errors='coerce')
x_vals = df.index.tolist()

# --- Option: Save plots as PDFs ---
SAVE_TO_PDF = True  # Set to False to display plots instead
PDF_DIR = "pdfs"

if SAVE_TO_PDF:
    os.makedirs(PDF_DIR, exist_ok=True)


def finalize_plot(title, filename, use_loglog=False):
    plt.xlabel('Scale (Input Size)')
    plt.ylabel('Execution Time / Value')
    plt.title(title)
    plt.legend(loc='upper left', bbox_to_anchor=(1.05, 1))
    plt.grid(True, which="both", ls="-", alpha=0.3)

    if use_loglog:
        plt.xscale('log')
        plt.yscale('log')

    plt.tight_layout()

    if SAVE_TO_PDF:
        path = os.path.join(PDF_DIR, f"{filename}.pdf")
        plt.savefig(path)
        print(f"Saved: {path}")
        plt.close()
    else:
        plt.show()


all_cols = df.columns.tolist()


# --- f2p2f_close columns ---
f2p2f_close_cols = all_cols[all_cols.index("f2p2f_close/reader_reader"):all_cols.index("f2p2f_close/db") + 1]

if f2p2f_close_cols:
    plt.figure(figsize=(10, 6))
    for col in f2p2f_close_cols:
        label = col.replace("f2p2f_close/", "")
        plt.plot(x_vals, df[col], marker='o', label=label)
    finalize_plot('Translation from FOAS to PHOAS to FOAS', filename='f2p2f_close', use_loglog=False)
else:
    print("No f2p2f_close columns found in the dataset.")


# --- vcgen columns ---
vcgen_cols = all_cols[all_cols.index("vcgen/reader_reader"):all_cols.index("vcgen/db") + 1]

if vcgen_cols:
    plt.figure(figsize=(10, 6))
    for col in vcgen_cols:
        label = col.replace("vcgen/", "")
        plt.plot(x_vals, df[col], marker='o', label=label)
    finalize_plot('VC generation with Let and Assign', filename='vcgen', use_loglog=False)
else:
    print("No vcgen columns found in the dataset.")


# --- Recursion Analysis: Linear vs Log-Log ---
recursion_cols = [c for c in df.columns if 'vcgen_recursion' in str(c)]

if recursion_cols:
    # 1. Linear Recursion Plot
    plt.figure(figsize=(10, 6))
    for col in recursion_cols:
        label = col.replace("vcgen_recursion/", "")
        plt.plot(x_vals, df[col], marker='s', label=label)
    finalize_plot('VC generation with Recursion (Linear Scale)', filename='vcgen_recursion_linear', use_loglog=False)

    # 2. Log-Log Recursion Plot
    plt.figure(figsize=(10, 6))
    for col in recursion_cols:
        valid_mask = df[col] > 0
        label = col.replace("vcgen_recursion/", "")
        plt.plot(np.array(x_vals)[valid_mask], df[col][valid_mask], marker='s', label=label)
    finalize_plot('VC generation with Recursion (Log-Log Scale)', filename='vcgen_recursion_loglog', use_loglog=True)
else:
    print("No recursion columns found in the dataset.")