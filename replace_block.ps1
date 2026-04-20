$filePath = "e:\Dropbox\GitHub\lean4\Peano\Peano\PeanoNat\Combinatorics\GroupTheory\Sylow\Sylow.lean"
$content = [System.IO.File]::ReadAllLines($filePath)
$total = $content.Count
Write-Host "Total lines: $total"

# Find start (0-based): line containing "Infraestructura de rotaci"
$startLine = -1
for ($i = 0; $i -lt $content.Count; $i++) {
    if ($content[$i] -match "Infraestructura de rotaci") {
        $startLine = $i
        Write-Host "Start line (0-based): $startLine -> $($content[$i].Trim())"
        break
    }
}

# Find end (0-based): first line with "private theorem exists_ne_of_nodup_length_ge_two {"
$endLine = -1
for ($i = 0; $i -lt $content.Count; $i++) {
    if ($content[$i] -match 'private theorem exists_ne_of_nodup_length_ge_two \{') {
        $endLine = $i
        Write-Host "End line (0-based): $endLine -> $($content[$i].Trim())"
        break
    }
}

if ($startLine -eq -1 -or $endLine -eq -1) {
    Write-Error "Could not find markers!"
    exit 1
}

# New block content
$newBlock = @'
    -- ─── Infraestructura de rotación iterada ─────────────────────────────────

    private def nthRotate {α : Type} : ℕ₀ → List α → List α
      | 𝟘,    l => l
      | σ n', l => nthRotate n' (rotateList l)

    private theorem nthRotate_succ_comm {α : Type} (k : ℕ₀) (l : List α) :
        nthRotate k (rotateList l) = rotateList (nthRotate k l) := by
      induction k generalizing l with
      | zero => rfl
      | succ k' ih => exact ih (rotateList l)

    private theorem nthRotate_add {α : Type} (k₁ k₂ : ℕ₀) (l : List α) :
        nthRotate (add k₁ k₂) l = nthRotate k₁ (nthRotate k₂ l) := by
      induction k₁ generalizing l with
      | zero =>
        simp only [zero_add]
        rfl
      | succ k₁' ih =>
        rw [succ_add k₁' k₂]
        show nthRotate (add k₁' k₂) (rotateList l) =
             nthRotate k₁' (rotateList (nthRotate k₂ l))
        rw [ih (rotateList l), nthRotate_succ_comm k₂ l]

    private theorem nthRotate_mul_period {α : Type} (l : List α) (k : ℕ₀)
        (h : nthRotate k l = l) (n : ℕ₀) : nthRotate (mul n k) l = l := by
      induction n with
      | zero => rw [zero_mul]
      | succ n' ih =>
        rw [succ_mul n' k, nthRotate_add (mul n' k) k l]
        rw [h]; exact ih

    private theorem nthRotate_append_general {α : Type} :
        ∀ (n : ℕ₀) (ys zs : List α), lengthₚ ys = n →
        nthRotate n (ys ++ zs) = zs ++ ys := by
      intro n
      induction n with
      | zero =>
        intro ys zs h
        cases ys with
        | nil => simp [List.nil_append, List.append_nil]
        | cons b ys' => cases h
      | succ n' ih =>
        intro ys zs h
        cases ys with
        | nil => cases h
        | cons b ys' =>
          have h' : lengthₚ ys' = n' := by
            have : σ (lengthₚ ys') = σ n' := by simpa [lengthₚ_cons] using h
            injection this
          show nthRotate n' (rotateList ((b :: ys') ++ zs)) = zs ++ (b :: ys')
          have hrot : rotateList ((b :: ys') ++ zs) = ys' ++ (zs ++ [b]) := by
            simp [rotateList, List.append_assoc]
          rw [hrot, ih ys' (zs ++ [b]) h']
          simp [List.append_assoc]

    private theorem nthRotate_length_self {α : Type} (l : List α) :
        nthRotate (lengthₚ l) l = l := by
      have h := nthRotate_append_general (lengthₚ l) l [] rfl
      simp at h; exact h

    private theorem rotateList_fixed_all_eq {α : Type} (a : α) (xs : List α)
        (h : xs ++ [a] = a :: xs) : ∀ x ∈ xs, x = a := by
      induction xs with
      | nil => intro x hx; exact absurd hx List.not_mem_nil
      | cons b ys ih =>
        intro x hx
        simp only [List.cons_append] at h
        injection h with hba h_rest
        rcases List.mem_cons.mp hx with rfl | hy
        · exact hba
        · exact ih (hba ▸ h_rest) x hy

    private theorem nthRotate_fixed_all {α : Type} (l : List α)
        (h : rotateList l = l) (k : ℕ₀) : nthRotate k l = l := by
      induction k with
      | zero => rfl
      | succ k' ih =>
        show nthRotate k' (rotateList l) = l
        rw [h]; exact ih

    private theorem gpow_comm_left (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems) (n : ℕ₀) :
        G.op g (gpow G g n) = G.op (gpow G g n) g := by
      have h1 : gpow G g (add 𝟙 n) = G.op g (gpow G g n) := by
        rw [gpow_add G hg 𝟙 n, gpow_one G g hg]
      have h2 : gpow G g (add n 𝟙) = G.op (gpow G g n) g := by
        rw [gpow_add G hg n 𝟙, gpow_one G g hg]
      rw [← h1, add_comm 𝟙 n, h2]

    private theorem listProd_all_eq_gpow (G : FinGroup) (a : ℕ₀)
        (ha : a ∈ G.carrier.elems) (l : List ℕ₀) (hl : ∀ x ∈ l, x = a) :
        listProd G l = gpow G a (lengthₚ l) := by
      induction l with
      | nil => simp [listProd_nil, gpow_zero]
      | cons x xs ih =>
        have hx : x = a := hl x List.mem_cons_self
        have hxs : ∀ y ∈ xs, y = a := fun y hy => hl y (List.mem_cons_of_mem x hy)
        rw [listProd_cons, hx, ih hxs, lengthₚ_cons, gpow_succ]
        exact gpow_comm_left G ha (lengthₚ xs)

    -- ─── gcd y argumento de Bézout ────────────────────────────────────────────

    open Peano.Arith in
    private theorem gcd_eq_one_of_pos_lt_prime (k p : ℕ₀) (hk_pos : lt₀ 𝟘 k)
        (hk_lt : lt₀ k p) (hp : Prime p) : gcd k p = 𝟙 := by
      sorry

    open Peano.Arith in
    private theorem nthRotate_one_fixed_of_gcd_one {α : Type} (l : List α) (k p : ℕ₀)
        (hk : nthRotate k l = l) (hp_rot : nthRotate p l = l)
        (hgcd : gcd k p = 𝟙) : nthRotate 𝟙 l = l := by
      sorry

    -- ─── Longitud de allVectorsList ───────────────────────────────────────────

    private theorem nat_dvd_pow_pos (p n k : Nat) (h : p ∣ n) (hk : 0 < k) : p ∣ n ^ k := by
      induction k with
      | zero => omega
      | succ k' ih =>
        rw [Nat.pow_succ]
        cases k' with
        | zero => simpa [Nat.pow_zero]
        | succ k'' =>
          obtain ⟨q, hq⟩ := ih (Nat.succ_pos k'')
          exact ⟨q * n, by rw [hq]; ring⟩

    private def allVectorsFlatMap (elems : List ℕ₀) (n : ℕ₀) :
        List (Vector ℕ₀ n) → List (Vector ℕ₀ (σ n))
      | [] => []
      | v :: vs =>
        List.map (fun x => ⟨x :: v.val, by rw [lengthₚ_cons, v.property]⟩) elems ++
        allVectorsFlatMap elems n vs

    private theorem allVectorsFlatMap_length (elems : List ℕ₀) (n : ℕ₀)
        (recs : List (Vector ℕ₀ n)) :
        (allVectorsFlatMap elems n recs).length = recs.length * elems.length := by
      induction recs with
      | nil => simp [allVectorsFlatMap]
      | cons v vs ih =>
        simp only [allVectorsFlatMap, List.length_append, List.length_map,
                   List.length_cons, ih]
        omega

    private theorem allVectorsList_succ_length (elems : List ℕ₀) (n : ℕ₀) :
        (allVectorsList elems (σ n)).length =
        (allVectorsFlatMap elems n (allVectorsList elems n)).length := rfl

    private theorem allVectorsList_length (elems : List ℕ₀) (n : ℕ₀) :
        (allVectorsList elems n).length = elems.length ^ Ψ n := by
      induction n with
      | zero => simp [allVectorsList]
      | succ n' ih =>
        rw [allVectorsList_succ_length, allVectorsFlatMap_length, ih,
            isomorph_σ_Ψ, Nat.pow_succ]

    -- ─── Conteo de órbitas ───────────────────────────────────────────────────

    private theorem rotateVector_ne_fixed {n : ℕ₀} (v w : Vector ℕ₀ n)
        (hfixv : rotateVector v = v) (hw_ne : w ≠ v)
        (hpow : nthRotate n w.val = w.val) : rotateVector w ≠ v := by
      sorry

    private theorem mckay_orbit_count (p : ℕ₀) (hp : Prime p)
        (T : List (Vector ℕ₀ p))
        (hT_nodup : T.Nodup)
        (hT_rot : ∀ v ∈ T, rotateVector v ∈ T) :
        ∃ k : Nat, T.length =
          (T.filter (fun v => decide (rotateVector v = v))).length + Ψ p * k := by
      sorry

    private theorem mckay_p_dvd_powEqId (G : FinGroup) (p : ℕ₀)
        (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        p ∣ (ℕ₀FSet.filter (fun g => decide (gpow G g p = G.id)) G.carrier).card := by
      sorry

'@

# Build new file: lines 0..(startLine-1) + newBlock + lines endLine..end
$before = $content[0..($startLine - 1)]
$after = $content[$endLine..($content.Count - 1)]

$newLines = $before + $newBlock.Split("`n") + $after

Write-Host "New file will have $($newLines.Count) lines"
[System.IO.File]::WriteAllLines($filePath, $newLines, [System.Text.Encoding]::UTF8)
Write-Host "File written successfully"
