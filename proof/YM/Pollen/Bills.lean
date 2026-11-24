import YM.Pollen.Rill
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c N→L[ℂ]Fields c N) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c N⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
include H
lemma strokesZ (i:I)(s:List I)(Y:S): growsZ o Y (i::s).toFinset = growsZ o Y s.toFinset ∪ halo 1 {o i}:=by simp only [growsZ,List.toFinset_cons,biUnion_insert]; rw [union_comm (halo 1 _), Finset.union_assoc]
lemma cladU (X: Grid c)(x:P)(Y:S)(ht:clad (limits Y) x.val):clad (limits (growsZ o Y s.toFinset)) ((Φ X) s x).val:=by
   induction s with
   | nil=> rw [growsZ,List.toFinset_nil,biUnion_empty,union_empty]; exact ht
   | cons i s ih=> rw [eff_consU, strokesZ o V H]; exact Suit.stakes _ _ (H i) _ _ _ ih -- incl d? absent.H
lemma colorU (X:Grid c)(g:Frame c)(x:P): parcelColor N g I ((Φ (Lattice.gauge g X)) s x)= (Φ X) s (parcelColor N g I x):=by
     induction s with| nil=> rfl | cons i s ih=> rw [eff_consU, eff_consU, Suit.dyes _ _ (H i),ih]
lemma readsU (X Y:Grid c)(t0:S) (hu:Agrees (growsZ o t0 s.toFinset) X Y): (Φ X) s=(Φ Y) s:=by
    induction s with
    | nil=>rfl
    | cons i s ih=>ext u; rw [eff_consU,eff_consU]; rw [strokesZ o V H i] at hu; rw [Suit.holes _ _ (H i) X Y (agrees_mono hu subset_union_right),ih (agrees_mono hu subset_union_left)]
lemma measurableU {f:Grid c→P}(he:Measurable f): Measurable (fun V=> (Φ V) s (f V)):=by
    induction s with| nil=> exact he| cons i s ih=> exact Suit.spends _ _ (H i) ih
-- off-apert. all witnesses if actual paid hull spaced
local notation:max "Aŧ"=>Stitch.Tablet.credits
lemma vanishedU (X:Grid c)(p:P)(Y:S)(hp:clad (limits Y) p.val) (hv:Spaced o s.toFinset U.B)(ht:1<U.B*U.B)(hr:s.Nodup){i:I}(he:i∈s)(hx:o i∉Y): (Φ X) s p=0:=by
     induction s with
     | nil=>simp at he
     | cons j s ih=>
          have hZ0:=hr.of_cons; obtain ⟨hF,_⟩:=List.nodup_cons.mp hr; rw [eff_consU]; rw [List.toFinset_cons] at hv; rcases List.mem_cons.mp he with he|he
          · subst j; apply Suit.expires _ _ (H i) X _ _ _ (cladU o V H d s X p Y hp); intro h; rcases mem_union.mp h with h|h; exact hx h
            obtain ⟨j,hj,hx⟩:=mem_biUnion.mp h; obtain ⟨x,hx',hj'⟩:=halo_spec.mp hx; rw[mem_singleton.mp hx'] at hj'; exact Nat.not_le_of_lt ht ((hv _ (mem_insert_of_mem hj) _ (mem_insert_self ..) (fun hp=> hF (hp ▸ List.mem_toFinset.mp hj))).trans hj')
          have hh: (Φ X) s p=0:= ih (fun k hh j hj h=> hv k (mem_insert_of_mem hh) j (mem_insert_of_mem hj) h) hZ0 he; rw [hh,map_zero]
lemma spectralU (X:Grid c)(Y:Finset I)(x:P)(hx:Polite q Y x)(he:¬ Disjoint s.toFinset Y): (Φ X) s x=0:=by
    induction s with
    | nil=>simp at he
    | cons i s ih=>
        rw [eff_consU]; by_cases h0:Disjoint s.toFinset Y; swap; · rw [ih h0,map_zero]
        have hi:i∈Y:= not_not.mp fun ht=> he (by rw [List.toFinset_cons,← singleton_union]; exact disjoint_union_left.mpr ⟨(by simp [ht]),h0⟩); let f:= ((H i).bean X).twirl I; let z:= echoI (Keys c N) i; have hY: Polite q (s.toFinset∪Y) ((Φ X) s x):=pay_pieceU _ _ d s hx; have hv: Polite q (s.toFinset∪Y) (f ((Φ X) s x)):= politeStep _ hY rfl; change (d i) • (z*_)=0; exact Eq.trans (congr_arg ((d i) • ·) ((itOwn (A:=Keys c N) i).nilpotent hv (by simp [hi]))) (smul_zero ..)
lemma briskU(X: Grid c)(Y:Finset I)(x:P)(hj:{j:I | j∈s}.Nonempty)(h:ValidPieces (Keys c N) q univ x): ValidPieces (Keys c N) q univ ((Φ X) s x) ∧ pluck (Keys c N) ∅ ((Φ X) s x)=0:=by
     have hx z (b:Polite q z (Cupola.pick (Keys c N) q z x)):=b -- syntax
     have hf(k:Finset I):= pay_pieceU _ (fun i=>(H i).bean X) d s (choseTuft (Keys c N) q k x);
     rw [h.wholeV]; rw [map_sum]; refine ⟨ValidPieces.cost _ _ fun i _=> ValidPieces.role _ (hf _) (subset_univ _),?_⟩; rw [map_sum]; obtain ⟨i,hh⟩:=hj; exact sum_eq_zero fun j _=> (hf _).spectral _ ((burstPos q (((show s.toFinset.Nonempty from ⟨i,List.mem_toFinset.mpr hh⟩).mono subset_union_left ))).ne_empty.symm)
lemma shutU (X:Grid c)(Y:Finset I)(x:P)(he:¬ s.toFinset ⊆ Y): shutter (Keys c N) Y ((Φ X) s x)= 0:=by
     induction s with
     | nil=>simp at he
     | cons i s ih=>
           rw [eff_consU,Bean.restrict_at]; split; next hx=> rw [ih (fun hp=> he (by rw [List.toFinset_cons]; exact insert_subset hx hp)),map_zero] -- signature
           rfl
lemma spendsU (X:Grid c)(p:P){t b:ℝ}(ht:0<t)(hc:0 ≤ a)(hp:0 ≤ b)(hf:∀ i,‖d i‖≤ b): Stitch.Tablet.credits t ((Φ X) s p) ≤ (a*b)^s.length*(Aŧ t p):=by
     induction s with
     | nil=> rw[List.length_nil,pow_zero,one_mul]; exact le_rfl
     | cons i s ih=> rw[eff_consU]; apply (Suit.bills _ _ (H i) _ ht _).trans; rw[List.length_cons,pow_succ',mul_assoc (a*b)]; exact mul_le_mul ((mul_le_mul_of_nonneg_right (hf i) hc).trans_eq (mul_comm ..)) ih (load_nn ..) (mul_nonneg hc hp)
lemma phyU (X:Grid c){p:Grid c→P}{t b B:ℝ}(ht:0<t)(o':Site c) (hp:Phy t p X (U.dirBound o') U.order B 1)(k:ℕ) (he:∀ i∈s,separation (o i) o'≤ k)(ha:0 ≤a)(hb:0≤ b)(hv:∀ i,‖d i‖ ≤ b) : Phy t (fun Z=> (Φ Z) s (p Z)) X (U.dirBound o') U.order ((a*b)^s.length * B) (1+(s.length:ℝ)*(1+(k:ℝ))^U.power):=by
     induction s with
     | nil=> simp only [List.length_nil,pow_zero,one_mul, Nat.cast_zero,zero_mul,add_zero]; exact hp
     | cons i s ih=>
         let Q:=1+(s.length:ℝ)*(1+(k:ℝ))^U.power; have hm:0≤ Q:=(by unfold Q; positivity); have hx:= Suit.post (d i) i (H i) X ht o' (ih (fun i hi=>he _ (List.mem_cons_of_mem _ hi))) hm; refine hx.more ?_ (le_trans (add_nonneg (pow_nonneg (by positivity) _) hm) le_rfl) ?_
         · rw [List.length_cons,pow_succ',mul_assoc (a*b)]; exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (hv i) ha).trans_eq (mul_comm ..)) (mul_nonneg (pow_nonneg (mul_nonneg ha hb) _) hp.nn)
         rw [List.length_cons,Nat.cast_add,Nat.cast_one]; apply le_trans (add_le_add_left (pow_le_pow_left₀ (show (0:ℝ) ≤1+(separation (o i) o':ℝ) from (by positivity)) (add_le_add_right (Nat.cast_le.mpr (he i (List.mem_cons_self ..))) _) _) _) (le_of_eq ?_); ring -- reorder add_le_add_left/right names.
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.phyU
#print axioms YM.MassiveQCD.Sample.Basal.readsU
