import YM.Clink.Spoon
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C C' α α':ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder
variable {I:Type}(F:I→ Pulse c→Bundle)(X Y:I→ℝ)(i j:I→ Site c)(V:I→Support c)
def StrongR (o:Site c)(A:St c)(p: BudgetPoint)(σ T K:ℝ): Prop:= ∃ (I:Type)(_ : Fintype I)(Z:I→ParcelZ (c:=c)), Trust Z p σ T K ∧ (∀ i,o∈(Z i).R)∧ A=∑ i,(Z i).val
-- group by exact. threshold estimate with their Ω widths. γ = from donations.
structure Forum (p:BudgetPoint)(b n B:ℕ)(η C:ℝ):Prop where
     ht: p.threshold ≤η
     hL:B≤p.B
     power : p.power ≤ b
     orderP : p.order ≤ n
     nneg : 0 ≤ C
     goes(x y:Site c)(o:Site c)(V:Support c)(K:ℝ)(F:Pulse c→Bundle)(h:Crop x y η V F K)(h':o∈V)(X:Grid c)(l:List (Directions su c)) (hx:l≠[]) (htL:l.length ≤ p.order)(hy:∀ L∈l,p.dirBound o L) : ‖leftDerivs (F∘settled) l X‖ ≤ (1+(diameterQ B V:ℝ))^(b*n)*(C*K)*(p.threshold/η)
local notation "Ω" x:arg=> tribute B b n x
local notation "rT" x:arg=> Run.rent σ B x
variable (hV:∀ t, i t∈ V t∧ j t∈V t∧o∈V t)(h:∀ t, StockR (i t) (j t) (V t) p (F t) η (X t) (Y t))
include hV h
lemma ringF (hη: 0<η)(hh:0≤σ)(hF:Forum (c:=c) p b n B η C)(z: St c)(ht:∀ U:Grid c,z U=∑' t:I, blockL (i t) (j t) (F t (settled U)))(hv:∃ X':ℝ, HasSum (fun t=> Run.rent σ B (V t) * (Ω (V t) * X t)) X' ∧ X'≤ α)(hh':∃ Y':ℝ,HasSum (fun t=> Run.rent σ B (V t) * (Ω (V t) * Y t)) Y' ∧ Y'≤α'): StrongR o z p σ α (α'+C*α*(p.threshold/η)):=by
        obtain ⟨PX,hPX,hpk⟩:=hv; obtain ⟨PY,hPY,hpw⟩:=hh'
        let D:={u:Tick c // u.1∈u.2.2∧ u.2.1∈u.2.2 ∧ o∈u.2.2}; let u(t:I):D:=⟨(i t,j t,V t),hV t⟩
        let X0(t:I):= (rT (V t)) * (Ω (V t) * X t); let Y0(t:I):= (rT (V t))*(Ω (V t)* Y t); let A(X:I→ℝ)(t:D):=∑' l:{l:I// u l=t},X l.val
        let Z(t:D):ParcelZ (c:=c):=⟨t.val.1,t.val.2.1,t.val.2.2,fun U:Grid c=>∑' l:{l // u l=t},F l.val (settled U)⟩
        let f(t:D):= Ω (t.val.2.2) * A X t; let g(t:D):= Ω (t.val.2.2) *(A Y t+C*A X t*(p.threshold/η)); have hu(t): (u t).val=(i t,j t,V t):=rfl
        have hrL(x:Support c):1≤ (rT x):=Real.one_le_exp (by positivity) -- hh shadow
        have hZ9(x:Support c):1 ≤ Ω x:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) -- shadow
        have he (M:I→ℝ)(he:∀ i,0≤ M i)(hm:Summable fun i=> Run.rent σ B (V i)*(Ω (V i)*M i)): Summable M:= hm.of_nonneg_of_le he (fun i=> ((le_mul_of_one_le_left (he i) (hZ9 _)).trans (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans (hZ9 _)) (he i)) (hrL _))))
        have hX : Summable X:= he X (fun i=>(h i).crop.1) hPX.summable -- types shadow h fix
        have hY : Summable Y:= he Y (fun i=>(h i).nneg) hPY.summable
        have hZ(t:D): (Z t).Ticket p (f t) (g t) B:=by
             let E:={l//u l=t}; let P(q:E):=F q.val; let x:= t.val.1; let y:=t.val.2.1; let V':= t.val.2.2; have ht(Z:E): StockR x y V' p (P Z) η (X Z.val) (Y Z.val):=by obtain ⟨l,hl⟩:=Z; subst t; exact h l
             have hL:= StockR.stakes P (fun i=>X i.val) (fun i=>Y i.val) x y V' ht (hX.subtype _) hη (hY.subtype _); exact StockR.thorough x y V' _ t.property.1 t.property.2.1 hL hF.nneg hη hF.ht (fun i hi=> hF.goes _ _ _ _ _ _ hL.crop hi)
        have hK (z:I→ℝ)(y:ℝ)(hZ: HasSum z y): ∑ i:D,A z i=y:= (tsum_fintype ..).symm.trans (hZ.tsum_fiberwise u).tsum_eq
        have hS (z:I→ℝ)(t:D): Run.rent σ B t.val.2.2*(Ω t.val.2.2*A z t)= A (fun i=> rT (V i)*(Ω (V i)*z i)) t:=by
               unfold A; rw [←tsum_mul_left,←tsum_mul_left]; refine tsum_congr ?_; intro ⟨i,hk⟩; subst t; rfl
        have hg (z:D→ℝ)(w0:ℝ)(h:∀ i,0 ≤ z i) (ht: (∑ i:D,Run.rent σ B i.val.2.2*z i)≤ w0): Ac.Hit (fun i:D=>i.val.2.2) p.B z σ w0:=by
               intro i; apply budget_finite (fun j=>ite_nonneg (mul_nonneg (h j) (Real.exp_pos _).le) le_rfl); apply le_trans _ ht; apply sum_le_sum; intro j _; split
               next hv=> rw [mul_comm (z j)]; apply mul_le_mul_of_nonneg_right _ (h _); apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ ‹0≤σ›; exact_mod_cast YM.Next.Scheduling.cover_earns hF.hL _
               next _=> exact mul_nonneg (Run.fair ..).le (h _)
        refine ⟨D,inferInstance,Z,⟨f,g,fun _=>B,hZ,?_,?_⟩,fun i=>i.property.2.2,?_⟩
        · apply hg _ _ fun i=> (hZ i).tk; unfold f; simp_rw [hS]; change ∑ i:D,A X0 i ≤α; rw [hK X0 PX hPX]; exact hpk
        · apply hg _ _ fun i=> (hZ i).nt; let z':= p.threshold/η; have hx(i:D): Run.rent σ B i.val.2.2 *g i=A Y0 i + C*A X0 i*z':=by
                 unfold g X0 Y0 z'; rw [← hS X,←hS Y]; ring
          simp_rw [hx]; rw [sum_add_distrib,←sum_mul,←mul_sum,hK _ _ hPX,hK _ _ hPY]; exact add_le_add hpw (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpk hF.nneg) (div_nonneg p.threshold_pos.le hη.le))
        funext U; let P(i):=(Z i).f U; let J0(t:I):=blockL (i t) (j t); let S(t:I):= F t (settled U); let g(t:D):= blockL t.val.1 t.val.2.1; have he:Summable S:=hX.of_norm_bounded fun i=> (h i).crop.2.2.2.1 _ (citizenship _ hη U)
        let X':= fun k:I=> J0 k (S k); have hJ(t:D)(l:{l:I//u l=t}): g t (S l.val)=J0 l.val (S l.val):=congr_arg (fun t=> g t (S l.val)) l.property.symm
        have hz' : Summable X':= by -- fiber finite
              let L:D→ℝ:= fun i=>‖g i‖; let M:=∑ i:D,L i
              have hm: Summable fun i:I=> M*‖S i‖:= he.norm.mul_left M
              refine hm.of_norm_bounded ?_; intro i; exact ((g (u i)).le_opNorm (S i)).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun (i:D) _=>norm_nonneg (g i)) (mem_univ (u i))) (norm_nonneg _))
        have hh(t:D): (Z t).val U=∑' i:{l:I//u l=t}, X' i.val:=by change g t _= _; unfold g X'; change blockL _ _ (∑' i:{l:I//u l=t},S i.val)=_; rw[ContinuousLinearMap.map_tsum _ (show Summable fun i:{l:I//u l=t}=> S i.val from he.subtype _)]; exact tsum_congr (hJ t)
        rw[ht, Finset.sum_apply]; simp_rw[hh]; exact (hz'.hasSum.tsum_fiberwise u).tsum_eq.symm.trans (tsum_fintype ..)
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.ringF
