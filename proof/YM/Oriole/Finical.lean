import YM.Oriole.Pop
import YM.Oriole.Indigo
/-! Two levels off-shell classification with third root convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)(g:Bool)
open Poised.Display Poised.Stative Module Finset Revolve
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
local notation "G"=> pulp g
variable (p q:Multi d)(D:CensusA d)(M:Spike)(s:Signed)
lemma low (p:Multi d): 3 ≤ spinWeight p:= Nat.le_add_right ..
lemma ground_iff : order (power p)=0 ↔ p=0:=by
     constructor; · intro h; apply Subtype.ext; funext i; apply Fin.ext; exact Nat.eq_zero_of_le_zero (le_trans (single_le_sum (f:=power p) (fun _ _=> Nat.zero_le _) (mem_univ i)) h.le)
     rintro rfl; have he(i:Axis):power (0:Multi d) i=0:=rfl;
     simp [order,he]
lemma ground (h:spinWeight p ≤3): p=0:=by unfold spinWeight at h; apply (ground_iff p).mp; omega
lemma nectar (i j:Axis): power (UV.first i) j= if i=j then 1 else 0:=by simp [UV.first,power,Pi.single_apply,ite_apply,eq_comm]; split <;> simp_all [eq_comm]
lemma nectarH(i:Axis): order (power (first i))=1:=by unfold order; simp_rw [nectar]; simp
lemma juicy(i:Axis): spinWeight (first i)=5:=by rw[spinWeight,nectarH]
lemma highV(i:Axis): first i≠0:=by intro h; have h' := juicy i; rw[h,cost_root] at h'; contradiction
lemma first_eq {i j:Axis}: first i=first j ↔ i=j:=by
      constructor; · intro h; have h' : power (first i) i=power (first j) i:=congr_arg (fun k=>power k i) h; rw [nectar,nectar] at h'; split at h'; split at h'; exact Eq.symm (by assumption); simp at h'
                     next ht=> contradiction
      rintro rfl; rfl
lemma halo (p:Multi 8)(h:spinWeight p ≤5)(ht:p≠0):∃ i:Axis, first i=p:=by
     unfold spinWeight at h; let f:=power p; have hv:order f≠0:= (ground_iff p).not.mpr ht; have hL:order f=1:=by unfold f at *; omega
     obtain ⟨i,hi⟩:∃ i:Axis,f i≠0:=by contrapose! hv; unfold order; simp only [hv,sum_const_zero]
     refine ⟨i,?_⟩; apply Subtype.ext; funext j; apply Fin.ext; change power (first i) j= _; rw[nectar]; have hu:f i≤1:= le_trans (single_le_sum (f:=f) (fun _ _=> Nat.zero_le _) (mem_univ i)) hL.le; have he:f i=1:=by omega
     split_ifs with hx
     · subst j; exact he.symm
     have ht : f i + f j ≤1:=le_trans (?_: _ ≤ order f) hL.le; change 0=f j; omega
     unfold order; rw [← sum_pair hx]; apply sum_le_sum_of_subset_of_nonneg (subset_univ _); intro i _ _; exact Nat.zero_le _
lemma hem_ground(d:ℕ) : hem s (0:Multi d)=0:=by apply (ground (hem s (0:Multi d))); rw [borderBuck,cost_root]
lemma hem_first(i:Axis): hem s (first i)=first (s.perm i):=by
     apply Subtype.ext; funext j; apply Fin.ext; change power (hem _ _) _=power _ j; rw [hemming,nectar,nectar]; split_ifs with hx h h; · rfl
     · exact False.elim (h (s.perm.eq_symm_apply.mp hx))
     · exact False.elim (hx (s.perm.eq_symm_apply.mpr h))
     rfl
lemma vital(i:Axis): marked s (first i)= signT s i:=by unfold marked; rw [prod_eq_single i]; rw [nectar,if_pos rfl,pow_one]; intro b _ h; simp [nectar,h.symm]; simp

variable (x: Label d)(h:a≠b)(hx:CharmC a b x.val)
local notation "Z" => juncoat x.val
noncomputable def Wings (g:Bool)(p:Pol d):Prop:= ∀ (w: EuPin)(s:Signed), w.Lifts s→ ∀ z:ℂ, conjug w (pulp g)=z • pulp g → pinAct w p=z • p
-- apply to value line at 0
variable (ht: Wings g x.val)
include hx h ht
lemma taste (hd:d ≤8)(w:EuPin)(s:Signed)(hw:w.Lifts s)(z:ℂ)(hz:conjug w G=z • G) : z • assay a b (hem s p) (hem s q) Z= ((marked s p*marked s q:ℝ):ℂ) • conjug w (assay a b p q Z):=by
    obtain ⟨hQ,hY⟩:= feathers a b x hd h hx
    have he:= ht _ _ hw _ hz; have hh:tintP w Z = z • Z:= inj_coat (by unfold tintP; rw [← turning Z w, map_smul,hQ]; exact he)
    exact (giltA ..|>.symm).trans (hh ▸ pockets a b p q Z s w hw (by rw [hQ]; exact x.property))
lemma beam0 (hd:d ≤8): ∃ c:ℂ, assay a b (0:Multi d) (0:Multi d) Z=c • G:=by
     refine shine G _ (P_high _) fun i w hw=>?_ ; let s:=Signed.mirror i; obtain ⟨c,hc⟩:= chirP g s w hw; exact ⟨c,hc,by have hp:= taste a b g 0 0 x h hx ht hd w s hw c hc; rw [hem_ground, marked_root] at hp; simpa only [mul_one,Complex.ofReal_one,one_smul] using hp.symm⟩ -- args
omit ht hx
lemma bud6 (x':Label 6)(hx:CharmC a b x'.val) : ∃ X:Spike,x'.val=bilinear a b X 0 0:=by
      let D:= juncoat x'.val; let M:=assay a b 0 0 D
      obtain ⟨hQ,hY⟩:= feathers a b x' (by norm_num) h hx
      have he:D= fieldB a b 0 0 (wave M):=by
          ext ⟨⟨p,i⟩,e⟩ ⟨⟨q,j⟩,f⟩; rw[fieldK]; split; next h=> change p=0∧ e=a∧ q=0∧ f=b at h; obtain ⟨h1,h2,h3,h4⟩:=h; subst p e q f; exact congr_fun (congr_fun (king a b 0 0 D (hQ.symm ▸ x'.property)) i) j
          next ht=>
             by_contra hv; obtain ⟨he,hf,hM⟩:=hY _ _ hv
             change spinWeight p+spinWeight q≤6 at hM; have h1:=low p; have h2:=low q; exact ht ⟨ground p (by omega), he,ground q (by omega), hf⟩
      exact ⟨M,hQ.symm.trans ((congr_arg (fun x=> jcoat x) he).trans (j_stard ..))⟩
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.beam0
#print axioms YM.Massive.Oriole.bud6
