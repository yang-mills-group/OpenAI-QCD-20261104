import YM.Bloom.Shrimp
/-! # convert body matrices native costs. opaque Fintypes explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom
open Function Lattice Laurent Bloch Metric RG Filter
open Finset YM.Bank Precision Matrix Exterior Arise Arise.Range Jar
open YM.Bank.Jule Ivo Pic Maxwell Hypnos Hypnos.Fruit TreeP
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {G:Gauge}{c f:Side}{k m j B B₀ r L n D d:ℕ}{a b u v t s W A T ε C y' z' ψ:ℝ}
-- arbitrary inst.
abbrev count0 (G:Gauge)(c:Side):Fintype (Col G c):= inferInstance
variable (U':Fintype (Col G f))(X':Fintype (Col G c))
variable (p:Zinc G k)(q:Zinc G m)(x y:Cover)(h:Eyes G D L (2*n) j a v b ε s C)
variable (g: Ratio c f)(J: Matrix (Body 2 f) (Body 2 c) ℝ)(F H:Bed) (ht:Fare j a b g J F H)
variable {R: Matrix (Col G f) (Col G c) ℂ}
private lemma adapt {A:Type}(U V:Fintype A)(P:Fintype A→Prop)(h:P U):P V:=(Subsingleton.elim U V) ▸ h
private lemma adaptP {A B:Type}(U V:Fintype A)(X Y:Fintype B)(P:Fintype A→ Fintype B→ Prop)(h:P U X):P V Y:=by rw [Subsingleton.elim V U,Subsingleton.elim Y X]; exact h
-- macro lemma cleanup using exact old via revert U' X'
local notation "Mp"=> pots W f p x
local notation "Np"=> pots W f q y
local notation "𝕄"=> paid G J
include h ht
lemma idea (hm:m≤ D)(hk:k≤ D)(hv:Factor W D g.count A) : ‖(Mp * (𝕄 * heartP H G c* (𝕄).transpose)* (Np).transpose) () ()‖ ≤ C*A^2:=by
    -- tactic `apply...`; force canonical by explicit normal def global normal.F
    rw [Subsingleton.elim U' (count0 G f),Subsingleton.elim X' (count0 G c)]; exact tilted p q h g J F H ht hv x y hk hm
lemma jump (hk:k ≤ D)(hs:L ≤ B₀)(hv:Factor W D g.count A)(o:Site c)(hr:∀ i, i∈ clique G f 2 B₀ (wrap f x) →∀ v,R i v≠0 → v∈ clique G c 2 B o) (hR:∀ i,cusp (paid G J-R) i≤ T) (hT:0 ≤ T)(U:Directions G c)(hz:‖U‖ ≤ y')(hW:|ψ⁻¹|≤ z') : cusp (Mp *paid G J*jetO G c ψ U) ()≤ z'*(crop G W C T A D B*y'):=by
    rw [Subsingleton.elim X' (count0 G c)] at hR; rw [Subsingleton.elim U' (count0 G f),Subsingleton.elim X' (count0 G c)]; exact light_view p x h g J F H ht hv hk hs o R hr hR hT U hz hW
    -- syntax tactic
omit ht h
lemma violet (hq:Eyes G D L (2*n) j a v b ε s C)(hp:k ≤ D)(hm:m ≤ D) (F:Bed)(hF: Grain a v b F f)(hw:1≤W) : ‖(Mp*heartP F G f*(Np).transpose) () ()‖ ≤ billN W D*(billN W D*C):=by rw [Subsingleton.elim U' (count0 G f)]; exact idolV p q x y hq hp hm F hF hw
lemma pens (hq: Acquired G D n a v b ε s C W f)(hp:k ≤ D)(hm:m ≤ D)(F:Bed)(hF: Grain a v b F f) (hv: posT W (2*n) (x-y)∈ Oasis ε s): ‖(pots (W^n) f p x*heartP F G f*(pots (W^n) f q y).transpose) () ()-viewK p q (posT W (2*n) (x-y))‖ ≤ C/W:=by rw [Subsingleton.elim U' (count0 G f)]; exact hq.title k hp m hm p q x y F hF hv
lemma marks(hq:Eyes G D L (2*n) j a v b ε s C)(hp:k ≤ D)(hw: 1 ≤ W) : cusp Mp () ≤ billN W D*C:=by rw [Subsingleton.elim U' (count0 G f)]; exact costume p hq hp x hw -- order
end YM.Bloom
#print axioms YM.Bloom.idea
#print axioms YM.Bloom.jump

#print axioms YM.Bloom.marks
