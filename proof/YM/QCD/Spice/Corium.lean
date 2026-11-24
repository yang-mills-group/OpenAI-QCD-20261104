import YM.QCD.Spice.Bloom
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
lemma workman {x:Site f}{y: Site c}{d: Ratio c f}(U:Support f)(ht:x∈U)(hp:d.embed y∈U): meets d x m' y ≤ (10*(l+1:ℝ))^m' * (1+(coverNumber l U:ℝ))^m' :=by
   have hr : separation (d.parent x) y ≤ (coverNumber l U)*(4*l+2)+2*l+1:=by
      have hm := YM.Work.E04.parent_separation d x (d.embed y); rw [d.embed_parent] at hm; exact hm.trans (Nat.add_le_add_right (Corona.extent _ l ht hp) _)
   have hh : (separation (d.parent x) y:ℝ) ≤ (coverNumber l U:ℝ)*(4*(l:ℝ)+2)+2*l+1:=by exact_mod_cast hr
   rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); have hx : 0 ≤ (l:ℝ)*(coverNumber l U:ℝ):=by positivity
   linarith only [hh,Nat.cast_nonneg (α:=ℝ) (coverNumber l U),Nat.cast_nonneg (α:=ℝ) l,hx]
section
-- support for every direction crop.H independent.
variable {ι E:Type*}[Fintype ι][Fintype E] {H:Grid f→ArrayL ι E}{P:Land f ι E}{Y:Pays f ι E}{f':ι→Site f}{c':E→Site f}
variable (hp:Pack f' c' δ u l H q P Y) (o:Site f)(p:Site c)(i:ι)(r:E)(d:Ratio c f)
variable (he:0<δ)(hx0:h₀ ≤ u)
include hp
lemma petty (U:Grid f)(hQ:p∉spanM d o b)(ht:d.embed p=f' i ∨ d.embed p=c' r) (he:0<δ) : spoon P o b i r (settled U)=0:=by
    by_contra! H; have hz:= trimming hp o b i r; have ht' := hz.2.1 (((norm_pos_iff.mpr H).trans_le (hz.2.2.2.1 _ (citizenship f he U))).ne'); exact hQ (mem_filter.mpr ⟨mem_univ _,ht.elim (fun h=>h ▸ ht'.1) (fun h=>h ▸ ht'.2)⟩)
lemma inside_fee {Y': Bundle} (he:0<δ)(hτ:0≤u)(hg:o=f' i∨o=c' r)(U:Grid f)(hx: beamAt (trunkFt o b) U 1 w)(hb:0≤w)(ht:w<δ/2)(hM:‖cell (H 1) i r-Y'‖≤ C): ‖spoon P o b i r (settled U) - Y'‖ ≤ C+(Real.exp (-u*fossil b l)+w/(δ/2)) *duel Y i r u l:=by
    let A:=spoon P o b i r; have hd:=trimming hp o b i r; have hh := cruise hd hx he ht hb; have h': 0≤ w/(δ/2):=div_nonneg hb (half_pos he).le
    refine le_trans (norm_sub_le_norm_sub_add_norm_sub (A (settled U)) (A (settled 1)) Y') ?_; exact (add_le_add (hh.trans (mul_le_mul_of_nonneg_right (coins hp o b i r hτ) h')) ((norm_sub_le_norm_sub_add_norm_sub _ (cell (H 1) i r) _).trans (add_le_add (mismatch hp i r b o hg hτ he _) hM))).trans_eq (by ring)
include hx0 he
lemma shadowM (hQ:p∉ spanM d o b)(hz:∀ n:ℕ,(1+(n:ℝ))^b₀ ≤ ζ*Real.exp (h₀ * n))(hv:o=f' i ∨ o=c' r)(ht:d.embed p=f' i∨d.embed p=c' r)(hy':0≤ζ): meets d o b₀ p* ‖cell (H 1) i r‖ ≤ ((10*(l+1:ℝ))^b₀ * ζ)* (Real.exp (-(u-h₀)*fossil b l)*duel Y i r u l):=by
    rw [produce hp o b,petty hp o p i r d _ hQ ht he, zero_add] -- direct use argument
    apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun k _=> (hp.crop i r k).2.2.2.1 _ (citizenship f he 1))) (meets_nn ..)).trans
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (worthZ hp i r o h₀ b hv hx0) (by positivity :0 ≤ (10*(l+1:ℝ))^b₀*ζ))
    rw [mul_sum,mul_sum]; apply sum_le_sum; intro k _; by_cases H:Y i r k=0
    · rw [H,mul_zero,mul_zero,mul_zero]; -- error
    have hh:= (hp.crop i r k).2.1 H; have hk : meets d o b₀ p≤ (10*(l+1:ℝ))^b₀* (1+(coverNumber l k:ℝ))^b₀:=workman _ (hv.elim (fun h=> h ▸ hh.1) (fun h=> h ▸ hh.2)) (ht.elim (fun h=> h ▸ hh.1) (fun h=> h ▸ hh.2)) -- r₀
    rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (hp.crop i r k).1; exact hk.trans ((mul_le_mul_of_nonneg_left (hz _) (by positivity : 0 ≤ (10*(l+1:ℝ))^b₀)).trans_eq (mul_assoc ..).symm)
end
-- cost Y sum. unconstrained support but tail via masses
lemma sailor {X:Ratio c f}{d: Site f}{Q V: Site c→ ℝ}{A:Site c→ℝ}(hq:0≤Q)(h:0 ≤ t)(hv:0≤w)(hK:0≤ D)(hp:0≤V)(he:∑ i,Q i ≤ v)(ht:∑ i,V i≤ v) (hh:∀ i∈spanM X d b, A i≤ D+t*Q i)(hP:∀ i,A i ≥0)(hl:∀ i,i∉spanM X d b→meets X d l i * A i≤w*V i) : ∑ i:Site c,meets X d l i*A i≤ (1+(b+1:ℝ))^l*((2*(b:ℝ)+1)^4*D+t*v)+w*v:=by
    let B:= (1+(b+1:ℝ))^l; let s:=spanM X d b
    let H i:=meets X d l i*A i; change ∑ j,H j ≤_
    rw [← sum_sdiff (subset_univ s),add_comm]; apply add_le_add
    · rw [mul_add]; apply le_trans (sum_le_sum (s:=s) (g:=fun i=> B*(D+t*Q i)) (fun i hi=> mul_le_mul (inwards X d hi l) (hh i hi) (hP i) (by unfold B; positivity)))
      rw [← mul_sum, sum_add_distrib, sum_const,nsmul_eq_mul,←mul_sum,←mul_add]
      exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (olives X d) hK) (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _=> hq i)).trans he) h)) (by unfold B; positivity)
    exact (sum_le_sum (fun i hi=> hl i (mem_sdiff.mp hi).2)).trans ((le_of_eq (mul_sum ..).symm).trans (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>hp i)).trans ht) hv))
end YM.QCD.Spice
