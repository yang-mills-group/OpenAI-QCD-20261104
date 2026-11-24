import YM.Rill.Yen
/-! Uniform symmetrized operator bound in choir. Power extinguishes exterior constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q: Choir}(L:Pollens P Q)(a:Axis)
variable (p:Strip Q)(d r:ℝ)(D I:ℕ) (hr:0<r)(hd:0 ≤ d)
variable (G:∀ d,Cottage P d)(hS:Sway C.S) {β e:ℝ}(hp:C.Path β e) {φ:ℕ→ℕ} (H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop) (hP:P.System)
private lemma stance (q:ℝ)(he:0 < q)(h:0 ≤ d):∃ w:ℝ,∃ p: Cover, 0 ≤ w∧ w≤ d∧d < w+q ∧w • basis a=digit q p :=by
    let n:= ⌊d/q⌋₊; let w:ℝ:= n*q; have hh:(n:ℝ) ≤ d/q:=Nat.floor_le (by positivity); have hp :d/q < (n:ℝ)+1:= Nat.lt_floor_add_one _; refine ⟨w,n • step a,(by unfold w; positivity), (le_div_iff₀ he).1 hh, lt_of_lt_of_le ((div_lt_iff₀ he).1 hp) (le_of_eq ?_),?_⟩
    · unfold w; ring
    unfold digit; ext i; simp [basis_eq,step,vector]; split_ifs <;> simp_all[w,mul_comm]
include H hp hS hφ hP G
abbrev marvel : Prop:=∀ (N D:ℕ),∃ m:ℕ,∃ A:ℝ,0 ≤ A∧∀ d r:ℝ,0 < d→0 < r → r ≤ 1 →∀ p: Strip Q,List.length p=N→slab p a d r→(∀ i∈p,i.2∈ Q.level D∧ ‖i.2‖ ≤ 1)→∀ (n:ℕ)(v:Fin n→ Strip Q),(∀ i,Sunny (v i) a)→∀ u, crestG L a n (tack p a d∘v) u ≤ (↑((A*r⁻¹^m)^2):ℂ)*crestG L a n v u
lemma skill: marvel L a:=by
    intro N D; obtain ⟨m,A,hA,H'⟩:= chargedF L a D N G hS hp H; refine ⟨m*N,A^N,by positivity,fun d r hd hr hx p hq hB hL n v hv u=>?_⟩
    obtain ⟨j,hj,hC,hv'⟩:= H' r hr hx; let k:=C.S.spacing j; obtain ⟨w,z,hw,hh,h',he⟩:= stance a d k (space0 _ _) hd.le
    have hR:r/2<r:= half_lt_self hr; let W:=A*r⁻¹^m; have hW: 1 ≤ W:= one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (one_le_inv₀ hr|>.mpr hx)); have hc:d < w+r/2:=by have hj:k<r/16:=hj; linarith
    have ha:manor p a w (r/2):= ⟨(suburb a hB hR).1,fun i hi=>⟨hR.le.trans (hB.2 _ hi).1,(hB.2 _ hi).2.trans (by linarith)⟩⟩
    have hK(x:TileV Q)(hp:x∈p):Privilege P Q j x.2 W ∧ Privilege P Q j (L.adj a x.2) W:=hv' ⟨_,(hL _ hp).1⟩ (hL _ hp).2
    let l:=echo (Q:=Q) a (d-w); let B:=l ∘ v; let V:=tack p a w; have ht:tack p a d ∘ v= V∘B:=by funext i; have hx:d=w+(d-w):=(add_sub_cancel ..).symm; unfold Function.comp V B tack l Function.comp; rw [role,←hx];
    rw [ht, show A^N*r⁻¹^(m*N)= W^p.length from (by unfold W; rw[hq,mul_pow,pow_mul])]
    have hB':0 ≤ d-w:=sub_nonneg.mpr hh; refine le_trans (packed L a p w (r/2) j W ha (half_pos hr) hw G hS hp H hφ hP ⟨_,he⟩ (by rwa[hq]) (by linarith) (fun i hi=>(hK i hi).1) ?_ hW B (fun i=>echo_sunny a _ (hv i) hB') u) (mul_le_mul_of_nonneg_left (Quilt.heat L a _ hB' G hS hp H hφ hP v hv u) ?_)
    · intro i hi; rcases List.mem_map.mp hi with ⟨y,hy,e⟩; subst i; rcases List.mem_map.mp hy with ⟨t,ht,rfl⟩; exact (hK t (List.mem_reverse.mp ht)).2
    exact Complex.zero_le_real.mpr (sq_nonneg _)
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.skill
