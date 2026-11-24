import YM.Giles.Nacre
import YM.Giles.Vote
/-! Probe cost tables: stable under finite sums and root support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
variable (U:BudgetPoint)(g:su.Color)(F Y: Grid c→ Lat.Fields c 6)
lemma heard (h:Allow U g F n a)(hn:F=ᶠ[𝓝 1] Y): Allow U g Y n a:=by
     refine ⟨frugal _ _ hn.symm h.alive,fun i j k=>?_ ,fun x hx i j k=>?_⟩; · rw[←hn.eq_of_nhds]; exact h.heatL ..
     rw [←tent_eq g Y F hn]; exact h.fire _ hx ..
lemma marSe(h:Allow U g (foil F Y) n a)(hn:1 ≤ n)(x:Cover)(hp:Nearby x)(hx:march x F=F)(ht:∀ᶠ p in 𝓝 (1:Grid c),IsUnit (F p)): Allow U g (foil F (march x Y)) n (4*2^U.power*a):= heard U g _ _ (mart U g _ h hn x hp) (course x F Y ht hx).symm
lemma merve(h:Allow U g (foil F Y) n a)(hn:1 ≤ n)(i:Axis)(hp:∀ x:Cover,march x F=F)(ht:∀ᶠ p in 𝓝 (1:Grid c),IsUnit (F p)): Allow U g (foil F (stunt i Y)) n (4*2^U.power*a):=by
     let z:Cover:= step i; have h0:= marSe U g F Y h hn z ⟨i,.inl rfl⟩ (hp _) ht; have h1:=marSe U g F Y h hn (-z) ⟨i,.inr rfl⟩ (hp _) ht
     let A(x):=foil F (march x Y); rw [guise]; change Allow U g ((1/2:ℂ) • (A z-A (-z))) n _; rw[sub_eq_add_neg,←neg_one_smul ℂ (A (-z))]
     let k:= 4*2^U.power*a; have hz:k=‖(1/2:ℂ)‖*(k+‖(-1:ℂ)‖*k):=by norm_num; ring
     rw [show 4*2^U.power*a=_ from hz]; apply firesM _ _ _ (firesS _ _ _ _ h0 (firesM _ _ _ h1 (-1) hn) hn) _ hn
lemma lump {b:ℝ} (h:Allow U g F n a)(ha:a≤b): Allow U g F n b := ⟨h.alive,fun p i j=> (h.heatL ..).trans ha,fun t hv p i j=> (h.fire _ hv ..).trans ha⟩ -- binder b
variable {V:Type*}
lemma sumsG (Z:V→Density c 6)(q:Finset V)(K:V→ℝ)(h:∀ i∈q,Allow U g (Z i) n (K i))(hn:1 ≤ n): Allow U g (∑ i∈q,Z i) n (∑ i∈q,K i):=by
    classical
    induction q using Finset.induction_on with
    | empty=>
       rw [sum_empty,sum_empty]; refine ⟨contDiffAt_const,fun p i j=>?_,fun y hv p i j=>?_⟩
       · simp [peaks]
       rw[show tent g (0:Density c 6) y= 0 from (by unfold tent; simp[Function.comp_def])]; simp [peaks]
    | insert i q hx ih=> rw[sum_insert hx,sum_insert hx]; exact firesS _ _ _ _ (h i (by simp)) (ih fun i hi=>h i (mem_insert_of_mem hi)) hn
-- generic read.Derivative multiplier currency
noncomputable abbrev scale_e (f:Site c →Site c→ℂ)(a:ℝ)(d:ℕ):Prop:=∀ u v:Site c,‖f u v‖ ≤ a*sepW 0 u v^d
variable (x:Lat.Fields c 6)(p:Flavor 6) (i j:Fiber)
lemma pupils (hx: peaks p i j x≤ a)(D:Site c→Site c→ℂ)(h:scale_e D C 2)(hv:0≤C): ‖reed p p i j D x‖≤ C*a:=by
    apply le_trans _ (mul_le_mul_of_nonneg_left hx hv); unfold peaks; simp_rw [Finset.mul_sum]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> norm_sum_le ..)).trans ?_); refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_ ; rw[norm_mul]; exact ((mul_le_mul_of_nonneg_right (h ..) (norm_nonneg _)).trans_eq (mul_assoc ..))
lemma tithe (H:∀ c:Side,Cray c)(hp: Dart r H)(hD:r≤ U.power): ∃ C:ℝ,0≤C ∧ ∀ (c:Side)(F:Density c 6)(a:ℝ)(n:ℕ)(p:Flavor 6)(i j: Fiber), Allow U g F n a→ peaks p i j (tent g F (H c)) ≤ C*a:=by
    obtain ⟨C,hC,hX⟩:= payout U g hp hD; refine ⟨C,hC.le,fun c F a n p i j h=>?_⟩
    let x:= C⁻¹ • H c; have he: tent g F (H c)=(C:ℂ) • tent g F x:=by rw [Complex.coe_smul,←map_smul]; unfold x; rw [smul_inv_smul₀ hC.ne']
    rw [he,p_scaled,Complex.norm_real,Real.norm_of_nonneg hC.le]; exact mul_le_mul_of_nonneg_left (h.fire x (hX c) ..) hC.le
-- complex directions too
noncomputable abbrev Chan (d:ℕ)(V:∀ c:Side,VerseL c):Prop:=∃ B:ℝ,0≤B∧∀ c i, ‖V c i‖ ≤ B*peg i.1 d
lemma Chan_fare(V: ∀ c:Side, VerseL c) (he: Chan r V)(hd:r ≤ U.power):∃ C:ℝ,0 ≤ C ∧ ∀ (c:Side)(F:Density c 6)(a:ℝ)(n:ℕ)(p:Flavor 6)(i j:Fiber), Allow U g F n a→ peaks p i j (rub g F (V c)) ≤ C*a:=by
    obtain ⟨C,hC,hX⟩:=he; let X(c:Side):Cray c:=fun i=>(V c i).re; let Y(c:Side):Cray c:= fun i=>(V c i).im
    have hp:Dart r X:=⟨C,hC,fun i j=> (show ‖(V i j).re‖ ≤ _ from Complex.abs_re_le_norm _).trans (hX ..)⟩
    have hv:Dart r Y:=⟨C,hC,fun i j=> (show ‖(V i j).im‖ ≤ _ from Complex.abs_im_le_norm _).trans (hX ..)⟩
    obtain ⟨A,hA,hF⟩:= tithe U g X hp hd; obtain ⟨B,hB,hH⟩:= tithe U g Y hv hd; refine ⟨A+B,add_nonneg hA hB,fun i F a n p q r h=>?_⟩
    change peaks _ _ _ (tent g F (X i)+I • tent g F (Y i))≤ _; refine (p_plus ..).trans ?_; rw[p_scaled,Complex.norm_I,one_mul,add_mul]; exact add_le_add (hF _ _ _ _ _ _ _ h) (hH _ _ _ _ _ _ _ h)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.merve
#print axioms YM.Massive.Patria.Gall.sumsG
#print axioms YM.Massive.Patria.Gall.Chan_fare
