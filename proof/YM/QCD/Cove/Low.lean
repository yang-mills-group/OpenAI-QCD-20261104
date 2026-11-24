import YM.QCD.Cove.Grey
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj MeasureTheory
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{f c: Side}{S: Ratio c f}{E D J: Type}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "I"=> Fj D E J
variable (g:Send S F D) (P:Rise f F E J)(t:ℝ) 

lemma ax_cont (s: Finset I): Continuous (fun U:Grid f=> axle g U s) := by
  let H (K: Finset D) (U:Grid f) := K.noncommProd (fun i=> bucks g i U) (by intro i _ j _ _; exact ((Commute.symm (roundP (roundP (g.hat U j i).symm).symm)).sub_left (by exact Commute.one_left _)).sub_right (Commute.one_right _))
  have he i: Continuous (fun U:Grid f=> bucks g i U):=by
     letI : NormedAlgebra ℚ (EndA R) := .restrictScalars ℚ ℂ _
     exact ((exp_continuous.comp (g.river i)).sub continuous_const)
  have hm s:Continuous (H s):=by
    induction s using Finset.induction_on with
    | empty=> exact continuous_const
    | insert i s hi ih=> rw [show H (insert i s)=(fun U=> bucks g i U * H s U) from funext fun U=> noncommProd_insert_of_notMem _ _ _ _ hi]; exact (he i).mul ih -- syntax
  exact hm (ops s)

lemma flag_s (s: Finset (Fj D E J)):MeasurableSet {U|closeS g P t s U} :=by
   rw [show {U|closeS g P t s U} = ⋃ Y : {Y:Support f // P.wish (spent s)=Y ∩ brimW g P s}, {U| flags t U=Y.val} by
     ext i; simp [closeS] ]
   exact MeasurableSet.iUnion fun i=> flags_measurable_eq ..

-- generic continuity of wipe with matrix entries
lemma wipeC : Continuous (fun x: (Water c f F) × Alg R=>wipe A B x.1 x.2) := by
  have h (i:R): Continuous (fun K:Water c f F=> wipe A B K (atom i)):=by
    rcases splits_index i with ⟨j,rfl⟩|⟨j,rfl⟩
    · simp_rw [wiper]; fun_prop
    simp_rw [tails]; exact continuous_const
  have hm (L:List R):Continuous (fun K:Water c f F=> wipe A B K (L.map atom).prod):=by
    induction L with
    | nil=>simp only [List.map_nil,List.prod_nil,map_one]; fun_prop
    | cons i L ih=>simp only [List.map_cons,List.prod_cons,map_mul]; exact (h i).mul ih
  have he(s:Finset R):Continuous (fun K:Water c f F=>wipe A B K (mono s)):=by obtain ⟨w,-,-,hw⟩:=expression s; rw [hw]; simpa only [List.map_ofFn] using hm (List.ofFn w)
  simp_rw [show (fun x: (Water c f F) × Alg R=>wipe A B x.1 x.2)=fun x=>∑ s, coef s x.2 • wipe A B x.1 (mono s) by
    funext x
    conv_lhs=>arg 2; rw [←write x.2]
    rw [map_sum]; simp_rw [map_smul] ]
  exact continuous_finsetSum _ (fun i _=> ((continuous_coef (i:Finset R)).comp continuous_snd).smul ((he i).comp continuous_fst))

lemma mortar (hp:P.Wave t)(s:Finset I): Measurable (fun U:Grid f=> made P t U s):=by
  unfold made; apply Measurable.mul
  · refine Finset.measurable_prod _ ?_; intro i _; exact ((exp_continuous (𝔸:=EvenA f F)).measurable.comp (P.ready t hp i)).sub measurable_const
  exact Finset.measurable_prod _ fun i _=>hp.budget i
lemma axial (hp:P.Wave t)(s:Finset I): Measurable (fun U:Grid f=> axle g U s (near A B (light _ (made P t U s)))):=by
  let W:Grid f→ Alg R:=fun U=> near A B (light (Keys f F) (made P t U s))
  have hh: Measurable W:= ((show Continuous (fun x : EvenA f F=> near A B (light _ x)) from (show Continuous (near A B) from (near A B).toLinearMap.continuous_of_finiteDimensional).comp (lightC _)).measurable).comp (mortar P t hp s)
  let Q := fun z: Grid f × Alg R=> axle g z.1 s z.2
  have hX:Continuous Q := Continuous.clm_apply (f:=fun z : Grid f × Alg R=> axle g z.1 s) ((ax_cont g s).comp continuous_fst) continuous_snd
  change Measurable (Q ∘ (fun U : Grid f=> (id U,W U)))
  haveI : SecondCountableTopology (Grid f):=inferInstance
  haveI : SecondCountableTopology (Alg R):=inferInstance
  apply hX.measurable.comp; apply measurable_id.prodMk hh
lemma tinted (hp:P.Wave t)(s: Finset I): Measurable (light _ ∘ dye g P t s):= by
  letI: MeasurableSpace (Water c f F):=borel _
  letI: BorelSpace (Water c f F):=⟨rfl⟩
  haveI : SecondCountableTopology (Water c f F):=inferInstance
  simp only [comp_def,dipping]
  haveI : SecondCountableTopology (Alg R):=inferInstance
  let Q := fun x: (Water c f F) × Alg R=>wipe A B x.1 x.2
  let X := fun U:Grid f=> axle g U s (near A B (light (Keys f F) (made P t U s)))
  have hpM : Measurable Q:=(wipeC (F:=F) (f:=f) (c:=c)).measurable
  change Measurable (Q ∘ (fun U:Grid f=> (g.shortP U, X U)))
  apply hpM.comp; exact Measurable.prodMk g.vibe.measurable (show Measurable X from axial g P t hp s)

lemma morals (hp:P.Wave t)(s:Finset I): Measurable (light _ ∘ hue g P t s):=by
  by_cases ht:P.spare (spent s); swap; · simp only [comp_def,hue,ht,false_and,if_false]; exact measurable_const
  simp only [comp_def,hue,ht,true_and, apply_ite (light _),map_zero]; apply Measurable.ite (flag_s g P t s) _ measurable_const; exact tinted g P t hp s
end YM.QCD.Cove
