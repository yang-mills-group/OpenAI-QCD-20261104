import YM.QCD.Nola.Fields
import YM.QCD.Kites.Speed
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι K κ A:Type*} {n : Side} {k:ℕ} [Fintype A]{p:A→Site n} {s t a b:ℝ}
-- pricing on letters.Scaled.
open Kites Pads
noncomputable def tyre (t:ℝ): Patio A →ₐ[ℂ] Patio A:= car (engine t A) (fun x h=> (Grass.exterior_parity _ x).trans (congr_arg _ h))
lemma swaysT (x:Patio A): light A (tyre t x)= engine t A x.val:=rfl
lemma outP (x: Patio A)(h:0<t):tyre t⁻¹ (tyre t x)=x:=by
    apply Subtype.ext; change engine _ _ (engine t A x.val)=x.val; rw [Kites.makes, inv_mul_cancel₀ h.ne']; unfold engine; rw [show Matrix.diagonal _=(1:Matrix A A ℂ) from ?_,change_one]; rfl
    ext i j; simp [Matrix.one_apply,Matrix.diagonal_apply]
lemma themes (S:Pads p ι κ) {r:Support n}{x: Patio A}(h:light _ x∈region (alphabet (p:=p) r)): light _ (tyre t x)∈region (alphabet (p:=p) r):=by
    rw [swaysT]; apply effects (engine t A) _ x.val h; intro i hi; unfold engine; rw [change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq]; exact Subalgebra.smul_mem _ (Creek.marked _ _ hi) _
namespace Pads
variable (S:Pads p ι κ) (b: ι ⊕ κ→ℝ)(hp:∀ i,0 ≤ b i)
variable (he:∀ i, ‖tyre t (S.source i)‖ ≤ b (.inl i)) (ht:∀ i x, load (fun _=> t) (S.buys i x) ≤ b (.inr i)* load (fun _=> t) x)
def valueT (i:S.Join):= tyre t (S.unite i) -- t inference? implicit
noncomputable def taxon (i:S.Join):ℝ :=∏ j∈i.1,b j
include hp he ht
lemma better (s: Finset (ι⊕κ)): ‖tyre t (S.ham s)‖ ≤ ∏ j∈s,b j :=by
    let f(x:Patio A):= ‖tyre t x‖; let g (x:Alg A):=load (fun _=>t) x
    have hu (v :Finset κ)(x:Alg A): g (S.ping v x) ≤ (∏ i∈v,b (.inr i))*g x:=by
          induction v using Finset.induction_on generalizing x with
          | empty=>unfold g; simp [ping]
          | insert i v hi ih=> unfold ping; rw [noncommProd_insert_of_notMem _ _ _ _ hi]; change g (S.buys i (S.ping v x)) ≤ _; rw [prod_insert hi]; exact (ht i _).trans ((mul_le_mul_of_nonneg_left (ih x) (hp _)).trans_eq (mul_assoc ..|>.symm))
    let v:= s.toLeft; have hy:f (S.grape v) ≤ ∏ i∈v,b (.inl i):=by unfold f grape; rw [map_prod]; exact (Finset.norm_prod_le ..).trans (prod_le_prod (fun _ _=>norm_nonneg _) fun i _=> he i)
    refine le_trans (b:= (∏ i∈s.toRight,b (.inr i))* f (S.grape v)) (hu s.toRight _) ?_; refine (mul_le_mul_of_nonneg_left hy (prod_nonneg fun i _ => hp _)).trans_eq ?_; unfold v; rw [mul_comm]; conv_rhs=> rw [← Finset.toLeft_disjSum_toRight (u:=s),Finset.prod_disjSum]
omit hp he ht
variable {m:ℕ}(pR:ι⊕κ→ℝ)(hg:∀ i,0 ≤ pR i)(hL:∀ i,b i*tell (S.leaves i) m≤ pR i)
include hp hg hL
lemma tents (u:S.Join): taxon S b u * tell (unionK S u) m ≤ taxon S pR u:=by
     refine le_trans (mul_le_mul_of_nonneg_left (tarot S.leaves u.val u.property.1 m) (prod_nonneg (s:=u.val) (fun i _=> hp i))) ?_ ; unfold taxon; rw [← prod_mul_distrib]; exact prod_le_prod (fun i _=>mul_nonneg (hp i) (zero_le_one.trans (tell_one ..))) fun i _=>hL i
variable (χ ε:ℝ)
omit hp hL
lemma thirst (h: 0 ≤ ε)(he : Ac.HitCard S.leaves pR (ε+1) a)(hz: a ≤1)(ha:0≤a): Ac.HitCard S.unionK (S.taxon pR) ε (Real.exp a-1):=by
     intro x; have hh:= Ac.forestCard _ h hg he hz ha x; have hx:= budget_pull (fun j:S.Join => j.val) Subtype.val_injective hh; refine budget_mono hx (fun i=>?_) (fun i=>?_)
     · split
       · exact mul_nonneg (prod_nonneg (s:=i.1) (fun j _=>hg j)) (Real.exp_pos _).le
       exact le_rfl
     split
     next hi => apply le_of_eq; unfold Ac.rootsCard; rw [if_pos ⟨i.property.1,hi⟩]; unfold taxon; exact mul_comm ..
     next hi => exact hx.1 i
end Pads
end YM.QCD.Nola
