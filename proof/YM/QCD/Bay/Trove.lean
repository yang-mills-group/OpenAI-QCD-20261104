import YM.QCD.Bay.Cone
/-! # Weighted averaging packs: no loss in price or footprints. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {D V:Type*}[Fintype D][Fintype V][DecidableEq D][DecidableEq V]{f c: Side}{g:D→ Site f}{h:V→Site f}{δ A B t a:ℝ}{m:ℕ}
variable {s:Ratio c f}{P: Therm D s g}{Q:Therm V s h}{G:Grid f→ArrayL D V}{X:Land f D V}{Y:Pays f D V}

lemma paid_plus {H:Grid f→ArrayL D V}{W:Land f D V}{Z:Pays f D V}(hp:Pack g h δ t m G A X Y)(ht: Pack g h δ t m H B W Z): Pack g h δ t m (G+H) (A+B) (X+W) (Y+Z):=by
   have he i j: duel (Y+Z) i j t m=duel Y i j t m+duel Z i j t m:=by unfold duel; simp only [Pi.add_apply,mul_add,sum_add_distrib]
   refine ⟨fun i j S=>(hp.crop i j S).plus (ht.crop ..), fun i j S=> by simp only [Pi.add_apply,sum_add_distrib,hp.sells,ht.sells]; rfl, fun i=> ?_,fun j=>?_⟩
   · simp_rw [he,sum_add_distrib]; exact add_le_add (hp.spends _) (ht.spends _)
   simp_rw [he,sum_add_distrib]; exact add_le_add (hp.dues _) (ht.dues _)
lemma paid_const (hp:Pack g h δ t m G A X Y)(c:ℝ)(hc:0≤c): Pack g h δ t m (c • G) (c*A) (c • X) (c • Y):=by
   have he i j: duel (c • Y) i j t m=c*duel Y i j t m:=by unfold duel; simp only [Pi.smul_apply,smul_eq_mul,mul_sum]; apply sum_congr rfl; intro i _; ring
   constructor
   · intro i j S; have hx:=Crop.alloy (hp.crop i j S) (c:ℂ); rw [Complex.norm_real,Real.norm_of_nonneg hc] at hx; exact hx
   · intro i j U; simp only [Pi.smul_apply,← smul_sum,hp.sells]; rfl
   · intro i; simp_rw [he,←mul_sum]; exact mul_le_mul_of_nonneg_left (hp.spends _) hc
   intro j; simp_rw [he,←mul_sum]; exact mul_le_mul_of_nonneg_left (hp.dues _) hc
lemma assemble_p {I:Type*}(c:Finset I)(V:I→Grid f→ArrayL D V)(C:I→ℝ) (X:I→Land f D _)(Y:I→Pays f D _)(hv:∀ i∈c,Pack g h δ t m (V i) (C i) (X i) (Y i)): Pack g h δ t m (∑ i∈c,V i) (∑ i∈c,C i) (∑ i∈c,X i) (∑ i∈c,Y i):=by
  induction c using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact ⟨fun _ _ _=>Crop.zero,fun i j U=>by simp [cell]; rfl,fun i=>by simp [duel],fun j=>by simp [duel]⟩
  | insert i S hi ih=> rw [sum_insert hi,sum_insert hi,sum_insert hi,sum_insert hi]; exact paid_plus (hv _ (mem_insert_self ..)) (ih fun j hj=>hv j (mem_insert_of_mem hj))

structure Held (s:Ratio c f)(P:Therm D s g)(Q:Therm V s h)(F:Land f D V):Prop where
  kept (u:Strut c)(p:Site f→ℂ)(T:Spike)(h: Warrant (raise s u) p T) (U: Grid f)(i j S): F i j S (settled U)= driveD s P Q u T p F i j S (settled U)

lemma honors (hp: Pack g h δ t m G A X Y)(hv:Tow s P Q G) : ∃ X Y, Pack g h δ t m G A X Y ∧ Held s P Q X:=by
  let X₀:=fun i=> driveD s P Q i (sat (raise s i)) (ink (raise s i)) X
  let Y₀:=fun i=>driveC s P Q i Y
  let n:ℝ:= Fintype.card (Strut c); have hn:0<n:= by unfold n; exact_mod_cast Fintype.card_pos
  let Z:=n⁻¹ • (∑ i,X₀ i)
  let W :=n⁻¹ • (∑ i,Y₀ i)
  refine ⟨Z,W,?_,?_⟩ -- fix
  · have hh:= assemble_p univ (fun _=>G) (fun _=>A) X₀ Y₀ (fun i _=> costs s P Q hp hv i _ _ (assured _))
    have hm:= paid_const hh n⁻¹ (inv_pos.mpr hn).le
    simp only [sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℝ, show (Fintype.card _ :ℝ)=n from rfl,smul_eq_mul, ← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul,inv_smul_smul₀ hn.ne'] at hm; exact hm
  constructor; intro u p T he U i j S
  unfold Z
  have hA : (∑ i₀,X₀ i₀ i j S (settled U))=∑ v:Strut c,X₀ (pod u v) i j S (settled U):=(Equiv.sum_comp (skyEquiv u) (fun k=> X₀ k i j S (settled U))).symm -- placeholder
  simp only [Pi.smul_apply,Finset.sum_apply]; rw [hA]; unfold driveD tips
  simp only [Finset.sum_apply,Pi.smul_apply, Matrix.mul_sum,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_smul]
  apply congr_arg (n⁻¹ • ·); refine sum_congr rfl fun v _=> ?_ ; exact (courier U s P Q u v T _ p _ he (assured _) _ _ _ X).symm
end YM.QCD.Bay
