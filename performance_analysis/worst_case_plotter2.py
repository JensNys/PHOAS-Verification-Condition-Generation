import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import os

# 1. Load data
file_path = 'sequenced_if.xlsx'
df = pd.read_excel(file_path, index_col=0)

# Ensure the X-axis (index) is numeric
df.index = pd.to_numeric(df.index, errors='coerce')
x_vals = df.index.tolist()

# --- Option: Save plots as PDFs ---
SAVE_TO_PDF = False  # Set to False to display plots instead
PDF_DIR = "pdfs"

if SAVE_TO_PDF:
    os.makedirs(PDF_DIR, exist_ok=True)


def finalize_plot(title, filename, use_loglog=False, use_semilogy=False):
    plt.xlabel('Scale (Input Size)')
    plt.ylabel('Execution Time / Value')
    plt.title(title)
    plt.legend(loc='upper left', bbox_to_anchor=(1.05, 1))
    plt.grid(True, which="both", ls="-", alpha=0.3)

    if use_loglog:
        plt.xscale('log')
        plt.yscale('log')
    elif use_semilogy:
        plt.yscale('log')

    plt.tight_layout()

    if SAVE_TO_PDF:
        path = os.path.join(PDF_DIR, f"{filename}.pdf")
        plt.savefig(path)
        print(f"Saved: {path}")
        plt.close()
    else:
        plt.show()


# --- Sequenced If: Linear Plot ---
plt.figure(figsize=(10, 6))
for col in df.columns:
    plt.plot(x_vals, df[col], marker='o', label=col)
finalize_plot('Sequenced If (Linear Scale)', filename='sequenced_if_linear', use_loglog=False)

# --- Sequenced If: Semi-Log Plot (log Y axis) ---
plt.figure(figsize=(10, 6))
for col in df.columns:
    valid_mask = df[col] > 0
    plt.plot(np.array(x_vals)[valid_mask], df[col][valid_mask], marker='o', label=col)
finalize_plot('Sequenced If (Semi-Log Scale)', filename='sequenced_if_semilog', use_semilogy=True)

# --- Sequenced If: Log-Log Plot ---
plt.figure(figsize=(10, 6))
for col in df.columns:
    valid_mask = df[col] > 0
    plt.plot(np.array(x_vals)[valid_mask], df[col][valid_mask], marker='o', label=col)
finalize_plot('Sequenced If (Log-Log Scale)', filename='sequenced_if_loglog', use_loglog=True)