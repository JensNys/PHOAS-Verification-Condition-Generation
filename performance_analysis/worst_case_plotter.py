import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from sklearn.linear_model import LinearRegression
from sklearn.metrics import r2_score

# 1. Load data
file_path = 'worst_case_data.xlsx'
df = pd.read_excel(file_path, index_col=0)

# Ensure the X-axis (index) is numeric
df.index = pd.to_numeric(df.index, errors='coerce')
x_vals = df.index.tolist()

# Select only the 4th column
col = df.columns[3]
y_vals = df[col]
label = 'Worst Case'


def finalize_plot(title, use_loglog=False, use_semilogy=False):
    """General formatting for plots."""
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
    plt.show()


# Filter valid (positive) values for log plots
valid_mask = y_vals > 0
x_valid = np.array(x_vals)[valid_mask].reshape(-1, 1)
y_valid = y_vals[valid_mask]

# --- R² for semi-log (exponential fit: log(y) ~ x) ---
log_y = np.log(y_valid)
model = LinearRegression().fit(x_valid, log_y)
r2 = r2_score(log_y, model.predict(x_valid))
print(f"Semi-log R² (exponential fit): {r2:.6f}")


# 1. Linear Plot
plt.figure(figsize=(10, 6))
plt.plot(x_vals, y_vals, marker='o', label=label)
finalize_plot(f'{label} (Linear Scale)')

# 2. Semi-log Plot
plt.figure(figsize=(10, 6))
plt.plot(x_valid, y_valid, marker='o', label=f'{label} (R²={r2:.4f})')
finalize_plot(f'{label} (Semi-Log Scale)', use_semilogy=True)

# 3. Log-Log Plot
plt.figure(figsize=(10, 6))
plt.plot(x_valid, y_valid, marker='o', label=label)
finalize_plot(f'{label} (Log-Log Scale)', use_loglog=True)