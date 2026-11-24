import YM.QCD.Brick.Snow
/-! # Lift both legs off plane (moments of parent rotor). Exact prices for two old differences on both. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f:Side} {j k N m:ℕ}(B:Plan j)(F:Flight j k) (h:f.val=c.val*F.L.val){p r q t :ℝ}
set_option quotPrecheck false

def brawn (F:Flight j k)(r:Site F.L)(u:List Axis)(x:Cover):Bundle:=Matrix.of fun i j=> fonts F u r i j x
set_option maxHeartbeats 160000 in
lemma shores (hj:4≤j)(hk:4≤k) : ∃ σ C : ℝ,0<σ∧0≤C∧∀ (P:Flight j k)(r:Site P.L) (u:List Axis),u.length ≤2 → Width σ (C*slope P.L/(P.L.val:ℝ)^(1+u.length)) (brawn P r u):=by
   obtain ⟨σ,c,hσ,hc,H⟩:= reserves_font hj hk; obtain ⟨b,hb,V⟩:= Sparks.float_norm -- namespace
   let I:= Fiber × Fiber; let U:ℝ:= Fintype.card I * c
   refine ⟨σ,b*U,hσ,mul_nonneg hb (by unfold U; positivity),fun P r u hu=>?_⟩
   let f (i:I) (x:Cover):= ‖fonts P u r i.1 i.2 x‖
   have hv(x:Cover): ‖brawn P r u x‖≤ b*(∑ i:I,f i x):=by
      have ha (i:I):0 ≤ f i x:=norm_nonneg _
      apply V _ _ (sum_nonneg fun i _=> ha i); intro i j; change f (i,j) x≤_; exact single_le_sum (s:=univ) (f:=fun i=>f i x) (fun i _=>ha i) (mem_univ (α:=I) (i,j))
   let R':=c*slope P.L/(P.L.val:ℝ)^(1+u.length)
   let w (i:I) (x:Cover):=Real.exp (σ*size x)*f i x; have he (i:I):SumBudget (w i) R':= H P r u (by omega) i.1 i.2 -- hp only v.Y.Check
   have h : SumBudget (fun x=> ∑ i:I,w i x) ((Fintype.card I:ℝ)*R'):=by
      have hs : Summable (fun x=> ∑ i:I,w i x) := summable_sum (fun i _=> (he i).2.1) -- manual
      refine ⟨fun x=>sum_nonneg (fun j _=> (he j).1 x),hs,?_⟩
      rw [Summable.tsum_finsetSum (f:=fun i x=> w i x) fun i _=>(he i).2.1]; apply (sum_le_sum fun i _=> (he i).2.2).trans_eq; simp only [sum_const,card_univ,nsmul_eq_mul]
   have hl : ∀ x, Real.exp (σ*size x)*‖brawn P r u x‖ ≤ b*∑ i:I,w i x:=by
      intro i; unfold w; rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (hv i) (Real.exp_pos _).le).trans_eq (mul_left_comm ..)
   have he:= budget_mono (budget_scale hb h) (show ∀ x,0 ≤ Real.exp (σ*size x)*‖brawn P r u x‖ from fun _=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hl
   have ht: b*((Fintype.card I:ℝ)*R')=b*U*slope P.L/(P.L.val:ℝ)^(1+u.length):=by unfold U R'; ring
   exact budget_loosen he ht.le

lemma pearl (x y:Site c) (r:Site F.L) (u:List Axis)(hj:4≤j)(hk:4≤k)(hu:u.length≤2): HasSum (fun i=>caption F h (brawn F r u i) x y r i) (cell (oldDiff (proton F h) u) ((sliceL F h).assemble (x,r)) y):=by
  let ζ:=occ ((sliceL F h).embed x) (lift r)
  refine Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j=> ?_
  obtain ⟨σ,C,hσ,hC,H⟩:= reserves_font hj hk
  have he:= (splash_budget x y (((H F r u (by omega) i j).unweighted hσ.le).2.1)).of_norm.hasSum.mul_left ζ
  convert! he using 1
  · funext v; by_cases h:x+wrap c v=y<;>simp only [caption,h, Matrix.smul_apply,Matrix.zero_apply, ↓reduceIte,splashL, brawn,Matrix.of_apply,mul_zero]; ring
  change oldDiff (proton F h) u ((sliceL F h).assemble (x,r),i) (y,j)=_
  rw [eligible F h hj hk u (by omega)]; exact prints ..
def cape (s:Side)(n:ℕ):ℝ:=slope s*((s.val:ℝ)⁻¹)^(1+n)
lemma cape_pos (s:Side)(n:ℕ):0<cape s n:=by unfold cape; positivity [slope_pos s]
lemma caper (hj:4 ≤ j)(hk:4 ≤ k)(m:ℕ): ∃ C :ℝ, 0≤C∧∀ (F:Flight j k)(c f:Side)(h:f.val=c.val*F.L.val)(u:List Axis),u.length≤2→∀ x, ∑ y,meets (sliceL F h) x m y*‖cell (oldDiff (proton F h) u) x y‖ ≤ C*cape F.L u.length:=by
   obtain ⟨σ,C,hσ,hC,H⟩:= shores hj hk; obtain ⟨v,hv,h⟩:=eats m σ hσ
   refine ⟨v*C,mul_nonneg hv.le hC,fun F c f d u hu x=>?_⟩
   let R:=sliceL F d; let p:=R.parent x; let t:=R.residue x
   have hx:R.assemble (p,t)=x:= R.unpack_at x
   have he y:= pearl F d p y t u hj hk hu; unfold R at hx; simp_rw [hx] at he
   exact (scales p t _ _ h hv (H _ t u hu) _ he).trans_eq (by unfold cape; rw [inv_pow]; ring)
-- linear foot data
variable {R:Ratio c f}
local notation "M"=> Modes f N
local notation "T"=> Modes c N
abbrev railDay (X:Kit.Rail f c):Kit.Rail c f:= chirality c*Xᴴ*chirality f
lemma calm (X:Kit.Rail f c)(i j): ‖cell (railDay X) i j‖≤ ‖cell X j i‖:=by
   rw [railDay,Garden.halo,cell_flip]; have h:= Lat.rotation_price (show (Lat.wave g5)∈ unitary _ from ⟨by rw [wave_star,g5_star,wave_mul,g5_sq,wave_one],by rw [wave_star,g5_star,wave_mul,g5_sq,wave_one]⟩)
   apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) h).trans; apply (norm_mul_le ..).trans; rw [norm_star]; exact mul_le_of_le_one_left (norm_nonneg _) h
abbrev powerF (X:Kit.Rail f c):= bladesF (choir N X) (choir N (railDay X))
lemma duty (x:Keys f N) (y:Keys c N) (X : Kit.Rail f c): ‖powerF (N:=N) X x y‖≤ ‖cell X (locationP x) (locationP y)‖:=by
   rcases x with p|p <;> rcases y with q|q <;> simp only [powerF, bladesF]
   · change ‖(if p.2=q.2 then X p.1 q.1 else 0)‖ ≤ _; split
     · exact Cost.north (cell X p.1.1 q.1.1) p.1.2 q.1.2
     rw [norm_zero]; exact norm_nonneg _
   · exact norm_zero.le.trans (norm_nonneg _)
   · exact norm_zero.le.trans (norm_nonneg _)
   change ‖(if q.2=p.2 then _ else 0)‖≤ _; split
   · exact (Cost.north (cell (railDay X) _ _) _ _).trans (calm ..)
   rw [norm_zero]; exact norm_nonneg _
end YM.QCD.Brick
