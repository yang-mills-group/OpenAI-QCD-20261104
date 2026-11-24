import YM.QCD.Spice.Corium
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "S"=> sliceL G h
variable {ζ ρ μ C D A m:ℝ}{b₀ m':ℕ} {h₀:ℝ}
open Fork
variable {d r X' B:ℝ}
open Garden
def soil (P:Plan j)(L:Side)(b l:ℕ) (u δ w ζ q m a:ℝ)(k:ℕ):ℝ:= (1+(b+1:ℝ))^k*((2*(b:ℝ)+1)^4*(stamp P L *m*a⁻¹*massL L)+(Real.exp (-u*fossil b l)+w/(δ/2))*q) + (((10*(l+1:ℝ))^k * ζ)*Real.exp (-(u-u/2)*fossil b l))*q
local notation "T"=> pesto
variable {P:Plan j}{U:Offer 1 x y}{V:Offer 2 X' r}
lemma banks (H:Sun G c f h δ v q u a l (pesto P G h (trunkM U V d m f))) (H': Sun G c f h δ v q u a l (pesto P G h (trunkM U V d 0 f))) (b k:ℕ)(o:Site f)(X:Grid f)(hx:beamAt (trunkFt o b) X 1 w)(ht:w<δ/2)(hv:∀ n:ℕ,(1+(n:ℝ))^k≤ ζ*Real.exp (u/2*n))(hp:0≤w)(he:0< u)(hh:0 ≤ ζ):
    let M:=soil P G.L b l u δ w ζ q |m| a k
    (∑ i:Site c, Fork.meets S o k i*‖spoon H.Z o b o i (settled X)-cell (proton G h) o i‖)≤M ∧ (∑ i:Site c,Fork.meets S o k i*‖spoon H.V o b i o (settled X)-cell (barP G h) i o‖)≤M :=by
    intro M; let D:= (10*(l+1:ℝ))^k*ζ; let Y:= D*Real.exp (-(u-u/2)*fossil b l); have hδ:0<δ:=H.positive; have hY:0 ≤ Y:=by unfold Y D; positivity
    let θ:= Real.exp (-u * fossil b l)+w/(δ/2); have hθ:0≤θ:=add_nonneg (Real.exp_pos _).le (div_nonneg hp (half_pos hδ).le)
    let E₁:= stamp P G.L*|m| *a⁻¹*massL G.L; have hz:0≤ E₁:= (norm_nonneg _).trans ((fees H.stable).1 o 0)
    obtain ⟨h₁,h₂⟩:= fees H'.stable; simp only [abs_zero,mul_zero,zero_mul,norm_le_zero_iff, sub_eq_zero] at h₁ h₂
    let A i:=duel H.W o i u l; let Q i:=duel H'.W o i u l
    constructor
    · refine sailor (X:=S) (Q:=A) (V:=Q) (fun i=> (trimming H.Z0 o b o i).1.trans (coins H.Z0 o b o i he.le)) hθ hY hz (fun i=> (trimming H'.Z0 o b o i).1.trans (coins H'.Z0 o b o i he.le)) (H.Z0.spends o) (H'.Z0.spends o) (fun i _=> inside_fee H.Z0 o o i hδ he.le (Or.inl rfl) X hx hp ht ((fees H.stable).1 o i)) (fun i=>norm_nonneg _) ?_
      intro i hi; rw [petty H.Z0 o i o i S X hi (Or.inr rfl) H.positive,zero_sub,norm_neg, ← h₁ o i]; exact (shadowM H'.Z0 o i o i S hδ (half_le_self he.le) hi hv (Or.inl rfl) (Or.inr rfl) hh).trans_eq (mul_assoc ..).symm
    let A i:=duel H.B0 i o u l; let Q i:= duel H'.B0 i o u l
    refine sailor (X:=S) (Q:=A) (V:=Q) (fun i=> (trimming H.V0 o b i o).1.trans (coins H.V0 o b i o he.le)) hθ hY hz (fun i=> (trimming H'.V0 o b i o).1.trans (coins H'.V0 o b i o he.le)) (H.V0.dues o) (H'.V0.dues o) (fun i _=> inside_fee H.V0 o i o hδ he.le (Or.inr rfl) X hx hp ht ((fees H.stable).2 i o)) (fun i=>norm_nonneg _) ?_
    intro i hi; rw [petty H.V0 o i i o S X hi (Or.inl rfl) H.positive,zero_sub,norm_neg,← h₂ i o]; exact (shadowM H'.V0 o i i o S hδ (half_le_self he.le) hi hv (Or.inr rfl) (Or.inl rfl) hh).trans_eq (mul_assoc ..).symm
variable {T₀:Grid f→Sheet f} (Q:Sun G c f h δ v q u a l T₀)
-- Moment arm for any foam, supports both; also moment of difference via foam_sub
lemma foamSales {f c: Side}{L:Ratio c f} (X: Site f → Site c→ Bundle)(Y:Site c→ Site f → Bundle)(x:Keys f F)(K:ℝ)(k:ℕ)
    (hp: (∑ i: Site c,Fork.meets L (locationP x) k i*‖X (locationP x) i‖)≤K ∧ (∑ i:Site c,Fork.meets L (locationP x) k i*‖Y i (locationP x)‖)≤K): (∑ i:Keys c F,Fork.meets L (locationP x) k (locationP i)*‖foamB X Y x i‖) ≤ fingers F*K:=by
    let d:=locationP x; let A := Fork.meets L d k
    have ht:(∑ i:Modes c F, A (headF i)*‖X d (headF i)‖)≤fingers F*K:= (rowsSum c F (fun i=> A i*‖X d i‖)).trans_le (mul_le_mul_of_nonneg_left hp.1 (by unfold fingers; positivity))
    have hQ:(∑ i:Modes c F,A (headF i)*‖Y (headF i) d‖)≤fingers F*K:=(rowsSum c F (fun i=>A i*‖Y i d‖)).trans_le (mul_le_mul_of_nonneg_left hp.2 (by unfold fingers; positivity))
    cases x
    next x=> rw [Fintype.sum_sum_type]; simp only [foamLR,norm_zero,mul_zero,sum_const_zero,add_zero]; apply le_trans ?_ ht; refine sum_le_sum fun i _=>?_ ; apply mul_le_mul_of_nonneg_left _ (meets_nn ..); rw [foamI]; split; exact Cost.north (X _ _) _ _
             rw [norm_zero]; exact norm_nonneg _
    next x=> rw [Fintype.sum_sum_type]; simp only [foamRL,norm_zero,mul_zero,sum_const_zero,zero_add]; apply le_trans ?_ hQ; refine sum_le_sum fun i _=>?_ ; apply mul_le_mul_of_nonneg_left _ (meets_nn ..); rw [foamR]; split; exact Cost.north (Y _ _) _ _
             rw [norm_zero]; exact norm_nonneg _
lemma freezeQ (i:Keys f F)(U:Grid f) (p k:ℕ)(K:ℝ)(he:Sea G h p δ K q t Q.Z Q.V k)(hp:Healthy t (halo (p+1) {locationP i}) U):
    (∑ j:Keys c F,Fork.meets S (locationP i) k (locationP j)*‖(Q.equip F p).shortP U i j‖) ≤ fingers F*K := by
      let X x j :=spoon Q.Z x p x j (settled U); let Y j x:=spoon Q.V x p j x (settled U)
      change (∑ j:Keys c F,meets S (locationP i) k (locationP j)*‖foamB X Y i j‖)≤_; apply foamSales; obtain ⟨a,b⟩:=he (locationP i); obtain ⟨Y,hY,hy,hk⟩:= a.leases; obtain ⟨V,hV,hv,h⟩:=b.leases
      exact ⟨(sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (hk U hp j) (meets_nn ..))).trans hy,(sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (h U hp j) (meets_nn ..))).trans hv⟩
end YM.QCD.Spice
