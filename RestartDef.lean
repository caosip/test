/-
File B — the dependency you EDIT.

Test flow for the "Restart File" button:
  1. Open `RestartShow.lean` (File A) in Fuse — its `#eval` shows 1.
  2. Change the value below (e.g. 1 → 2) and save.
  3. File A still shows the OLD value: its Lean worker cached the import
     from when it first opened.
  4. Click "Restart File" on File A — it rebuilds this file and reloads
     the import, so File A now shows the new value.
-/

def restartValue : Nat := 1

#print restartValue
