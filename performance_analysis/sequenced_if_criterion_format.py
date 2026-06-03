import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import os

# 1. Load data
file_path = 'sequenced_if2.xlsx'
df = pd.read_excel(file_path)

# 2. Parse the Name column into series and x value
df['series'] = df['Name'].apply(lambda x: '/'.join(x.split('/')[:-1]).replace('if/', ''))
df['x'] = df['Name'].apply(lambda x: int(x.split('/')[-1]))

# 3. Pivot to wide format: rows = x values, columns = series
df_pivot = df.pivot(index='x', columns='series', values='Mean').sort_index()
x_vals = df_pivot.index.tolist()

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


# --- Linear Plot ---
plt.figure(figsize=(10, 6))
for col in df_pivot.columns:
    plt.plot(x_vals, df_pivot[col], marker='o', label=col)
finalize_plot('If (Linear Scale)', filename='if_linear', use_loglog=False)

# --- Semi-Log Plot ---
plt.figure(figsize=(10, 6))
for col in df_pivot.columns:
    valid_mask = df_pivot[col] > 0
    plt.plot(np.array(x_vals)[valid_mask], df_pivot[col][valid_mask], marker='o', label=col)
finalize_plot('If (Semi-Log Scale)', filename='if_semilog', use_semilogy=True)

# --- Log-Log Plot ---
plt.figure(figsize=(10, 6))
for col in df_pivot.columns:
    valid_mask = df_pivot[col] > 0
    plt.plot(np.array(x_vals)[valid_mask], df_pivot[col][valid_mask], marker='o', label=col)
finalize_plot('If (Log-Log Scale)', filename='if_loglog', use_loglog=True)