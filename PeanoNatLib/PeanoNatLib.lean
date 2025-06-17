-- PeanoNatLib.lean
-- Este archivo contendrá la definición de ℕ₀ y otras definiciones fundamentales.

def ExistsUnique {α : Type} (p : α → Prop) : Prop :=
  ∃ x, (p x ∧ (∀ y, (p y → y = x)))

syntax "∃¹ " ident ", " term : term
syntax "∃¹ " "(" ident ")" ", " term : term
syntax "∃¹ " "(" ident " : " term ")" ", " term : term
syntax "∃¹ " ident " : " term ", " term : term

macro_rules
  | `(∃¹ $x:ident, $p:term) => `(ExistsUnique (fun $x => $p))
  | `(∃¹ ($x:ident), $p:term) => `(ExistsUnique (fun $x => $p))
  | `(∃¹ ($x:ident : $t:term), $p:term) => `(ExistsUnique (fun ($x : $t) => $p))
  | `(∃¹ $x:ident : $t:term, $p:term) => `(ExistsUnique (fun ($x : $t) => $p))

inductive ℕ₀ : Type
  where
  | zero : ℕ₀
  | succ : ℕ₀ -> ℕ₀
  deriving Repr, BEq, DecidableEq

def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}

def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}

def idℕ₀ (n : ℕ₀) : ℕ₀ := n
def idNat (n : Nat) : Nat := n
def EqFnGen {α β : Type} (f : α → β) (g : α → β) :
    Prop :=
        ∀ (x : α), f x = g x
def Inv {α β : Type} (f : α → β) (g : β → α) :
    Prop :=
        ∀ (x : α), g (f x) = x
def EqFn {α : Type}
        (f : ℕ₀ -> α)(g : ℕ₀ -> α) : Prop :=
  ∀ (x : ℕ₀), f x = g x
def EqFn2 {α : Type}
        (f : ℕ₀ × ℕ₀ -> α)(g : ℕ₀ × ℕ₀ -> α) : Prop :=
  ∀ (x : ℕ₀), ∀ (y : ℕ₀), f (x, y) = g (x, y)
def EqFnNat {α : Type}
        (f : Nat -> α)(g : Nat -> α) : Prop :=
  ∀ (x : Nat), f x = g x
def EqFnNatNat {α : Type}
        (f : Nat -> α)(g : Nat -> α) : Prop :=
  ∀ (x : Nat), f x = g x

namespace Peano
  set_option trace.Meta.Tactic.simp true -- Si es relevante para definiciones aquí

  notation "σ" n:max => ℕ₀.succ n
  def cero : ℕ₀ := ℕ₀.zero
  notation "𝟘" => ℕ₀.zero

  /-- Definiciones básicas para PeanoNat -/
  def one : ℕ₀ := σ 𝟘
  def two : ℕ₀ := σ one
  def three : ℕ₀ := σ two
  def four : ℕ₀ := σ three
  def five : ℕ₀ := σ four
  def six : ℕ₀ := σ five
  def seven : ℕ₀ := σ six
  def eight : ℕ₀ := σ seven
  def nine : ℕ₀ := σ eight
  def ten : ℕ₀ := σ nine
  def eleven : ℕ₀ := σ ten
  def twelve : ℕ₀ := σ eleven
  def thirteen : ℕ₀ := σ twelve
  def fourteen : ℕ₀ := σ thirteen
  def fifteen : ℕ₀ := σ fourteen
  def sixteen : ℕ₀ := σ fifteen
  def seventeen : ℕ₀ := σ sixteen
  def eighteen : ℕ₀ := σ seventeen
  def nineteen : ℕ₀ := σ eighteen
  def twenty : ℕ₀ := σ nineteen
  def twenty_one : ℕ₀ := σ twenty
  def twenty_two : ℕ₀ := σ twenty_one
  def twenty_three : ℕ₀ := σ twenty_two
  def twenty_four : ℕ₀ := σ twenty_three
  def twenty_five : ℕ₀ := σ twenty_four
  def twenty_six : ℕ₀ := σ twenty_five
  def twenty_seven : ℕ₀ := σ twenty_six
  def twenty_eight : ℕ₀ := σ twenty_seven
  def twenty_nine : ℕ₀ := σ twenty_eight
  def thirty : ℕ₀ := σ twenty_nine
  def thirty_one : ℕ₀ := σ thirty
  def thirty_two : ℕ₀ := σ thirty_one
  def thirty_three : ℕ₀ := σ thirty_two
  def thirty_four : ℕ₀ := σ thirty_three
  def thirty_five : ℕ₀ := σ thirty_four
  def thirty_six : ℕ₀ := σ thirty_five
  def thirty_seven : ℕ₀ := σ thirty_six
  def thirty_eight : ℕ₀ := σ thirty_seven
  def thirty_nine : ℕ₀ := σ thirty_eight
  def forty : ℕ₀ := σ thirty_nine
  def forty_one : ℕ₀ := σ forty
  def forty_two : ℕ₀ := σ forty_one
  def forty_three : ℕ₀ := σ forty_two
  def forty_four : ℕ₀ := σ forty_three
  def forty_five : ℕ₀ := σ forty_four
  def forty_six : ℕ₀ := σ forty_five
  def forty_seven : ℕ₀ := σ forty_six
  def forty_eight : ℕ₀ := σ forty_seven
  def forty_nine : ℕ₀ := σ forty_eight
  def fifty : ℕ₀ := σ forty_nine
  def fifty_one : ℕ₀ := σ fifty
  def fifty_two : ℕ₀ := σ fifty_one
  def fifty_three : ℕ₀ := σ fifty_two
  def fifty_four : ℕ₀ := σ fifty_three
  def fifty_five : ℕ₀ := σ fifty_four
  def fifty_six : ℕ₀ := σ fifty_five
  def fifty_seven : ℕ₀ := σ fifty_six
  def fifty_eight : ℕ₀ := σ fifty_seven
  def fifty_nine : ℕ₀ := σ fifty_eight
  def sixty : ℕ₀ := σ fifty_nine
  def sixty_one : ℕ₀ := σ sixty
  def sixty_two : ℕ₀ := σ sixty_one
  def sixty_three : ℕ₀ := σ sixty_two
  def sixty_four : ℕ₀ := σ sixty_three

  notation "𝟙" => one
  notation "𝟚" => two
  notation "𝟛" => three
  notation "𝟜" => four
  notation "𝟝" => five
  notation "𝟞" => six
  notation "𝟟" => seven
  notation "𝟠" => eight
  notation "𝟡" => nine
  notation "𝔸" => ten
  notation "𝔹" => eleven
  notation "ℂ" => twelve
  notation "𝔻" => thirteen
  notation "𝔼" => fourteen
  notation "𝔽" => fifteen
  notation "𝔾" => sixteen
  notation "ℍ" => σ sixteen
  notation "𝕁" => σ seventeen
  notation "𝕂" => σ eighteen
  notation "𝕃" => σ nineteen
  notation "𝕄" => σ twenty
  notation "ℕ" => σ twenty_one
  notation "ℙ" => σ twenty_two
  notation "ℚ" => σ twenty_three
  notation "ℝ" => σ twenty_four
  notation "𝕊" => σ twenty_five
  notation "𝕋" => σ twenty_six
  notation "𝕌" => σ twenty_seven
  notation "𝕍" => σ twenty_eight
  notation "𝕎" => σ twenty_nine
  notation "𝕏" => σ thirty
  notation "𝕐" => σ thirty_one
  notation "ℤ" => σ thirty_two
  notation "ψ" => σ thirty_three
  notation "π" => σ thirty_four
  notation "δ" => σ thirty_five
  notation "γ" => σ thirty_six
  notation "ε" => σ thirty_seven
  notation "ζ" => σ thirty_eight
  notation "η" => σ thirty_nine
  notation "φ" => σ forty
  notation "ι" => σ forty_one
  notation "χ" => σ forty_two
  notation "λ" => σ forty_three
  notation "μ" => σ forty_four
  notation "ξ" => σ forty_five
  notation "ω" => σ forty_six
  notation "Γ" => σ forty_seven
  notation "Π" => σ forty_eight
  notation "𝕒" => σ forty_nine
  notation "𝕓" => σ fifty
  notation "𝕔" => σ fifty_one
  notation "𝕕" => σ fifty_two
  notation "𝕖" => σ fifty_three
  notation "𝕗" => σ fifty_four
  notation "𝕘" => σ fifty_five
  notation "𝕙" => σ fifty_six
  notation "𝕛" => σ fifty_seven
  notation "𝕞" => σ fifty_eight
  notation "𝕟" => σ fifty_nine
  notation "𝕡" => σ sixty
  notation "𝕢" => σ sixty_one
  notation "𝕣" => σ sixty_two
  notation "𝕤" => σ sixty_three
  notation "𝕪" => σ sixty_four

  /-- probaremos posteriormente que se trata de un isomorfismo-/
  def Λ(n : Nat) : ℕ₀ :=
    match n with
    | Nat.zero => 𝟘
    | Nat.succ k => σ (Λ k)

  /-- probaremos posteriormente que se trata de un isomorfismo-/
  def Ψ (n : ℕ₀) : Nat :=
    match n with
    | ℕ₀.zero => Nat.zero
    | ℕ₀.succ k => Nat.succ (Ψ k)

  instance : Coe Nat ℕ₀ where
    coe n := Λ n

  /--
     LA SIGUIENTE FUNCIÓN PRED ES ISOMORFA A LA FUNCIÓN NAT.PRED
     SE SATURA CUANDO SUSTRAENDO ES MAYOR QUE MINUENDO A CERO
  -/
  def τ (n : ℕ₀) : ℕ₀ :=
    match n with
    | ℕ₀.zero => 𝟘
    | ℕ₀.succ k => k

  /--
     LA SIGUIENTE FUNCIÓN PRED ES CHEQUEADA Y PREFERIBLE
     A LA FUNCIÓN NAT.PRED
     (NO ES ISOMORFA A LA FUNCIÓN NAT.PRED)
  -/
  def ρ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) : ℕ₀ :=
    match n with
    | ℕ₀.zero =>
      False.elim (h_n_neq_0 rfl)
    | ℕ₀.succ k => k

  theorem neq_1_0 : 𝟘 ≠ 𝟙 := by
    intro h
    cases h
    -- Si 𝟘 = 𝟙, entonces 𝟘 = ℕ₀.succ ℕ₀.zero, lo cual es una contradicción.

  theorem neq_2_0 : 𝟘 ≠ 𝟚 := by
    intro h
    cases h
    -- Si 𝟘 = 𝟚, entonces 𝟘 = ℕ₀.succ ℕ₀.succ ℕ₀.zero, lo cual es una contradicción.

  theorem neq_2_1 : 𝟙 ≠ 𝟚 := by
    intro h
    cases h
    -- Si 𝟙 = 𝟚, entonces 𝟙 = ℕ₀.succ 𝟘 = ℕ₀.succ ℕ₀.succ 𝟘 = 𝟚, lo cual
    -- nos lleva a 𝟘 = ℕ₀.succ 𝟘 = 𝟙 que es uns contradicción por neq_1_0

  theorem neq_3_0 : 𝟘 ≠ 𝟛 := by
    intro h
    cases h

  theorem neq_3_1 : 𝟙 ≠ 𝟛 := by
    intro h
    cases h

  theorem neq_3_2 : 𝟚 ≠ 𝟛 := by
    intro h
    cases h

end Peano

export Peano (
  cero one two three four five six seven eight
  nine ten
  eleven twelve thirteen fourteen fifteen
  sixteen seventeen
  eighteen nineteen twenty
  twenty_one twenty_two twenty_three
  twenty_four twenty_five
  twenty_six twenty_seven
  twenty_eight twenty_nine thirty
  thirty_one thirty_two
  thirty_three thirty_four thirty_five
  thirty_six
  thirty_seven thirty_eight thirty_nine
  forty forty_one
  forty_two forty_three forty_four forty_five
  forty_six forty_seven forty_eight
  forty_nine fifty fifty_one fifty_two
  fifty_three
  fifty_four fifty_five
  fifty_six fifty_seven fifty_eight
  fifty_nine sixty
  sixty_one sixty_two
  sixty_three sixty_four
  Λ Ψ τ ρ
  neq_1_0 neq_2_0 neq_2_1 neq_3_0 neq_3_1 neq_3_2
)
-- La definiciones de ℕ₀, ℕ₁ y ℕ₂ son globales y no necesitan
-- ser exportadas explícitamente si el archivo es importado.
-- Igualmente con las deficiniciones de idℕ₀, idNat,
-- EqFnGen, Inv, EqFn, EqFn2, EqFnNat y EqFnNatNat.
