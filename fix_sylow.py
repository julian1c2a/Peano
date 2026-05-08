#!/usr/bin/env python3
# Fix remaining errors in Sylow.lean

path = 'Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean'

with open(path, encoding='utf-8') as f:
    content = f.read()

original = content

# ── Fix 1: h_orb_part_zero (Error 6) ─────────────────────────────────────────
old6 = (
    "                  have h_orb_part_zero :\n"
    "                      (FSet.filter (fun y => !isFixed y) (FSet.filter inOrb\u2080 X)).card = \U0001d7d8 := by\n"
    "                    suffices \u2200 z \u2208 (FSet.filter inOrb\u2080 X).elems, isFixed z = true by\n"
    "                      have : (FSet.filter (fun y => !isFixed y) (FSet.filter inOrb\u2080 X)).elems = [] := by\n"
    "                        apply List.filter_eq_nil.mpr\n"
    "                        intro z hz\n"
    "                        simp only [Bool.not_eq_true]\n"
    "                        exact this z hz\n"
    "                      simp [FSet.card, FSet.filter, this, length\u209a]\n"
    "                    intro z hz\n"
    "                    simp only [FSet.filter, List.mem_filter] at hz\n"
    "                    obtain \u27e8_, hz_inOrb\u27e9 := hz\n"
    "                    rw [h_inOrb_only_x\u2080 z hz_inOrb]\n"
    "                    exact h_isfixed_x\u2080"
)

new6 = (
    "                  have h_orb_part_zero :\n"
    "                      (FSet.filter (fun y => !isFixed y) (FSet.filter inOrb\u2080 X)).card = \U0001d7d8 := by\n"
    "                    have hsplit := h_card_split_bool isFixed (FSet.filter inOrb\u2080 X)\n"
    "                    have hall_card : (FSet.filter isFixed (FSet.filter inOrb\u2080 X)).card =\n"
    "                        (FSet.filter inOrb\u2080 X).card := by\n"
    "                      have heq : FSet.filter isFixed (FSet.filter inOrb\u2080 X) = FSet.filter inOrb\u2080 X := by\n"
    "                        apply FSet.eq_of_mem_iff\n"
    "                        intro z\n"
    "                        simp only [FSet.filter, List.mem_filter]\n"
    "                        exact \u27e8fun h => h.1, fun h => \u27e8h, by\n"
    "                          rw [h_inOrb_only_x\u2080 z h.2]; exact h_isfixed_x\u2080\u27e9\u27e9\n"
    "                      rw [heq]\n"
    "                    rw [hall_card] at hsplit\n"
    "                    exact (add_cancel _ _ _ ((add_zero _).trans hsplit)).symm"
)

if old6 in content:
    content = content.replace(old6, new6, 1)
    print("Fix 1 (h_orb_part_zero): REPLACED")
else:
    print("Fix 1 (h_orb_part_zero): NOT FOUND")
    # Debug: show what's actually there
    idx = content.find('filter_eq_nil')
    if idx >= 0:
        print("  Nearby text (bytes):", repr(content[idx-200:idx+200].encode('utf-8')))
    else:
        print("  'filter_eq_nil' not found in file!")

# ── Fix 2: h_G_dvd (Error: hpow not in scope) ────────────────────────────────
old_hG = (
    "          have h_G_dvd : p \u2223 G.carrier.card :=\n"
    "            \u27e8Mul.mul (p ^ \u03c3 m') r, by rw [\u2190 mul_assoc, \u2190 hpow]; exact hr_eq\u27e9"
)

new_hG = (
    "          have h_G_dvd : p \u2223 G.carrier.card :=\n"
    "            \u27e8Mul.mul (p ^ \u03c3 m') r, by\n"
    "              have hpow_local : p ^ \u03c3 (\u03c3 m') = Mul.mul (p ^ \u03c3 m') p := pow_succ p (\u03c3 m')\n"
    "              rw [\u2190 mul_assoc, mul_comm p (p ^ \u03c3 m'), \u2190 hpow_local]\n"
    "              exact hr_eq.symm\u27e9"
)

if old_hG in content:
    content = content.replace(old_hG, new_hG, 1)
    print("Fix 2 (h_G_dvd): REPLACED")
else:
    print("Fix 2 (h_G_dvd): NOT FOUND")
    idx = content.find('hpow]; exact hr_eq')
    if idx >= 0:
        print("  Nearby text:", repr(content[idx-100:idx+50]))

if content != original:
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    print("File written.")
else:
    print("No changes made.")
