import YM.QCD.Kites.Returns
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
section
variable {A B: Type*} [Fintype A][Fintype B][DecidableEq A][DecidableEq B]
lemma desire (x: Dirac A): ber A (surf A x) = star (ber A x):= by
  have hv (u:Finset A): surf A (vol u)=vol u:=by
    induction u using Finset.induction_on with
    | empty=> rw [vol_empty,surf_one]
    | insert a s ha ih=>
      rw [vol_step _ _ ha,surf_mul,ih]; have he:surf A (pair a)=pair a:=by unfold pair; rw [surf_mul,surf_P,surf_M, mul_neg]; unfold bar psi; rw [Grass.atom_flip]; simp
      rw [he]
  rw [← write x]; simp only [map_sum, star_sum]
  refine sum_congr rfl fun i _=>?_
  by_cases hi:i=univ
  · subst i
    have he : mono (univ : Finset (Pairs A)) ∈ Grass.layer (Pairs A) (Fintype.card (Pairs A)) := homogeneous _
    rw [top_is _ he]; simp only [map_smulₛₗ,hv,map_smul,starRingEnd_apply,smul_eq_mul]; simp
  have hQ : Fintype.card (Pairs A) ≠ i.card := fun h => hi (eq_univ_of_card i h.symm)
  rw [map_smulₛₗ,map_smul,map_smul,Grass.discarded (homogeneous _) hQ, Grass.discarded (show surf A (mono i) ∈ Grass.layer _ i.card from exterior_layer _ (cc_degree (homogeneous _))) hQ]; simp
lemma gulf (x:Dirac B): surf _ (far A B x)=far A B (surf B x):=by
  have hp (L: List _): surf _ (far A B (L.map atom).prod)=far A B (surf B (L.map atom).prod):=by
     induction L with
     | nil=> simp [surf_one]
     | cons j L ih=> rw [List.map_cons,List.prod_cons,map_mul,surf_mul,surf_mul,map_mul,ih]; congr 1
                     cases j
                     next i=> change surf _ (pass _ (psi _))= pass _ (surf _ (psi _)); rw [pass_psi,surf_P,surf_P,pass_bar]
                     next i=> change surf _ (pass _ (bar _))=pass _ (surf _ (bar _)); rw [pass_bar,surf_M,surf_M,map_neg,pass_psi]
  have he s: surf _ (far A B (mono s))=far A B (surf B (mono s)):=by obtain ⟨w,-,-,hw⟩:=expression s; rw [hw]; simpa only [List.map_ofFn] using hp (List.ofFn w)
  rw [← write x]; simp_rw [map_sum,map_smul,map_smulₛₗ,RingHom.id_apply,he]
lemma poetic (x:Dirac (A⊕B)):surf B (marginal A B x)=marginal A B (surf (A⊕B) x):=by
  apply (perfect B).injective; apply LinearMap.ext; intro y; rw [show y=surf B (surf B (grade y)) from ?_,perfect_apply,perfect_apply,marginal_test,← gulf,← surf_mul,← surf_mul,desire,desire,marginal_test]; rw [scud]; simp
lemma surfS (x:Dirac A):surf A (exp x)=exp (surf A x):=NormedSpace.map_exp (rib A) (surf_cont _) x
lemma shoot (Q: Matrix B A ℂ)(x:Dirac A):surf B (sheath 1 Q x)=sheath 1 Q (surf A x):=by
    rw [Kit.sheath,Kit.sheath]; simp only [Complex.ofReal_one,inv_one,one_pow,one_smul]; rw [poetic,surf_mul,Sway.surge]
    have he:surf (A⊕B) (gauss (joinD 1 Q 0))=gauss (joinD 1 Q 0):=by
        unfold gauss; rw [surfS,surf_form]; have ht:star (joinD 1 Q 0)=joinD 1 Q 0:=by unfold joinD; simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        rw [ht]
    rw [he]
end
end YM.QCD.Globe
