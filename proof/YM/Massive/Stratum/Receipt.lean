import YM.QCD.Fog.Frost
/-!
# Widening the stationary-loop-book gradient prices

Use the actual lattice cover offset dilation. Compare
`length_weight` and the gradient charge in `Smoke.Gust`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lattice Wilson Finset Filter Function Metric Extra Iteration RG Placement Laurent Exterior Work.F08 Precision Bloch Matrix
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {L n c f : Side}{I:Type*}{η σ A C r:ℝ}{G:Gauge}{k:ℕ}

private lemma greater_length (ψ : Columns L) (a : Pattern G k) (r z) {η σ : ℝ} (he : 0 ≤ η) (hs : η ≤ σ*L.val) :
    η * (reasonG ψ a r z).atom.length ≤ σ * a.atom.length + 8*η*k + ∑ i, η*Laurent.size ((z i).2.1) := by
  have hL := side_pos L
  have hσ : 0 ≤ σ := nonneg_of_mul_nonneg_left (he.trans hs) hL
  unfold reasonG; dsimp only; rw [relocated_length,Nat.cast_add,Nat.cast_sum,mul_add]; push_cast
  unfold Atom.length; rw [Nat.cast_sum, mul_sum,mul_sum]; unfold endingG
  have hi (i : Fin k) : (η* (Laurent.size (carry r (a.atom.leg i).offset + alter (z i).2):ℝ)) ≤
      σ*(a.atom.leg i).length + 4*η + η * Laurent.size ((z i).2.1) := by
    have hx := offset_size (a.atom.leg i)
    have hf : (Laurent.size (a.atom.leg i).offset:ℝ) ≤ (a.atom.leg i).length := by
      exact_mod_cast hx.trans (Nat.le_add_right _ 4)
    calc
      _ ≤ η * ((Laurent.size (carry r (a.atom.leg i).offset) : ℝ) + Laurent.size (alter (z i).2)) := by
        gcongr; exact_mod_cast Laurent.size_add _ _
      _ ≤ η * ((Laurent.size (a.atom.leg i).offset / (L.val:ℝ)+4) + Laurent.size ((z i).2.1)) := by
        gcongr
        · exact carry_bound ..
        exact compassG _
      _ = (η/L.val) * Laurent.size (a.atom.leg i).offset + 4*η + η * Laurent.size ((z i).2.1) := by ring
      _ ≤ _ := by gcongr; exact (div_le_iff₀ hL).2 hs
  have hl := sum_le_sum fun i (_:i∈univ) => hi i
  rw [sum_add_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin, nsmul_eq_mul] at hl
  linarith


variable {ψ :Columns L}
lemma greater_muster (v:Pattern G k)(r:Site L){δ:ℝ}(hf:σ≤δ*L.val)(hs:0 ≤ σ)(he:0<η)(hk:σ≤η/2)(h:∀ j,(ψ (v.op j)).strip η A): Charged (fun i=> (reasonG ψ v r i).atom) σ (cashRegister k η A*v.atom.budget δ):=by
  let Δ:=fun p:CompassG=> size p.2.1; have ht:=Cost.pi (fun i=> cardsG v r i hs he hk (h i)); simp only [prod_const,card_univ,Fintype.card_fin] at ht
  have hm : 0≤ v.atom.budget δ:=by unfold Atom.budget Atom.magnitude; positivity
  let d:=Real.exp (η*(8*k)); unfold cashRegister; rw [mul_right_comm]
  apply Cost.mono (Cost.scale ht (d*v.atom.budget δ) (mul_nonneg (Real.exp_pos _).le hm)) (fun i=> by unfold Atom.budget Atom.magnitude; positivity)
  intro i
  have hp := greater_length ψ v r i hs hf
  have hv : σ * (reasonG ψ v r i).atom.length≤ δ*v.atom.length +η*(8*k)+∑ j, σ*(Δ (i j):ℝ):=by unfold Δ; apply hp.trans; gcongr δ*v.atom.length+?_+∑ j, σ*(size (i j).2.1:ℝ); nlinarith only [(by linarith : σ ≤ η),Nat.cast_nonneg (α:=ℝ) k,mul_le_mul_of_nonneg_right (by linarith : σ≤η) (Nat.cast_nonneg (α:=ℝ) k)]
  have hw : (reasonG ψ v r i).atom.magnitude= |∏ j,worthG ψ v r (i j) j| * v.atom.magnitude:= relocated_coeff ..
  unfold Atom.budget; rw [prod_mul_distrib,← Real.exp_sum, ← Finset.abs_prod]; apply (mul_le_mul_of_nonneg_left (Real.exp_monotone hv) (by unfold Atom.magnitude; positivity : 0 ≤ (reasonG ψ v r i).atom.magnitude)).trans_eq
  unfold d Δ; rw [hw,Real.exp_add,Real.exp_add]; ring

lemma broad_shucks (E:I→PairG G) {δ:ℝ}(hf:σ≤δ*L.val)(_hA:0≤A)(h:0<η)(he:0≤σ)(ht:σ≤η/2)(hp:∀ v:Axis,(ψ (some v)).strip η (A/(L.val:ℝ)^3))(hg:Palisade E δ C) : Palisade (shootG ψ E) σ (cashRegister 2 η A / (L.val:ℝ)^2*C):=by
  let w:ℝ:= L.val; have hw:0<w:=side_pos L
  let u:= cashRegister 2 η (A/w^3)
  have hh (i:I)(x: Site L): Charged (fun j=> (reasonG ψ (E i) x j).atom) σ (u*(E i).atom.budget δ):= greater_muster (E i) x hf he h ht (fun j=>by obtain ⟨a,hh⟩:=Option.isSome_iff_exists.mp (hg.1 i j); rw [hh]; exact hp a)
  have he' (i:I): 0 ≤ u*(E i).atom.budget δ:=Cost.nonneg (hh i 0)
  refine ⟨fun _ _=>rfl,fun _=> relocated_symm _ (hg.2.1 _) _ _ _,?_⟩
  have hx: cashRegister 2 η A/w^2=(Fintype.card (Site L):ℝ)*u:=by unfold u cashRegister; rw [site_card,Nat.cast_pow]; unfold w; field_simp
  rw [show cashRegister 2 η A/(L.val:ℝ)^2=_ from hx]; apply Cost.product (Cost.scale hg.2.2 _ (by unfold u cashRegister; have hx:= passage_pos h; positivity))
  intro i; rw [mul_assoc]; exact Cost.product (Cost.finite _ (he' i)) (hh i)
end YM.QCD.Smoke

namespace YM.QCD.Fog
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03 Voyage
open scoped Matrix Topology ContDiff BigOperators Classical Matrix.Norms.L2Operator
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a b d η Ω Θ:ℝ}{M: Before su u v E.J K N}
variable (V:Back E K j k p u v) {J:Plan j}{U:On}
def Ornament.trim (U:Ornament r c) (h:δ ≤ r)(hb:c ≤ b): Ornament δ b := {U with paid:= ⟨U.paid.1,U.paid.2.1, Charged.mono (A:=fun i=> (U.P i).atom) U.paid.2.2 h hb⟩ }
lemma Ornament.trim_page (U:Ornament r c) (h:δ ≤ r)(hb:c ≤ b): (U.trim h hb).page=U.page:=rfl

/-- No added loop price when transmitting at a wider width (within gauge limit and dilation).
Use old thinner width, or narrow transiently, for the *identity*, not for the output bill. -/
lemma stretch_loop (X:Avenue V η Ω Θ)(U:Ornament r b)(he:0<η)(hΩ:0≤Ω)(hΘ:0≤Θ)(hδ:0<δ)(hr:0<r)(ht:δ≤η/2)(hL:δ≤r*E.L.val):
    ∃ Y:Ornament δ (cashRegister 2 η (psiPrice Ω Θ)/(E.L.val:ℝ)^2*b),∀ i,Duet (litG V U.page i) (barG Y.page (V.chain.n i)):=by
  let vv:= min r (η/2)
  have hh:0<vv:=lt_min hr (by positivity)
  let A:=U.trim (δ:=vv) (min_le_left ..) le_rfl
  have ha (i:ℕ):= transferReceipt A.P he hh (min_le_right ..) A.paid (X.paidUp i)
  let P:= shootG (psi X.D X.D' X.T) U.P
  have hw: (Palisade P δ (cashRegister 2 η (psiPrice Ω Θ)/(E.L.val:ℝ)^2*b)):= by
     rw [← V.has]; have hD:= (X.paidUp 0)
     apply broad_shucks U.P (by rw [V.has]; exact hL) ?_ he hδ.le ht ?_ U.paid
     · unfold psiPrice; positivity
     intro v; exact psi_strip he hD.high hD.low hD.early hD.deep (some v)
  let N:Ornament δ (cashRegister 2 η (psiPrice Ω Θ)/(E.L.val:ℝ)^2*b):=⟨_,P,hw⟩
  exact ⟨N,fun i=>identical V X ((ha i).2 (V.port.forest i) (V.port.u i) V.path (V.port.critical i) (X.sworn i))⟩
end YM.QCD.Fog
#print axioms YM.QCD.Fog.stretch_loop
