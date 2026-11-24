import YM.Pollen.Bills
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
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
open Stretch
local notation "μ₀"=> ample N I
variable (F :Patron.Rail c (ample N I) D)
local notation "L"=> withdraw N o t
local notation "R"=> banknote N o t
local notation "qT" i:arg=> (F.addr i).place
omit H
noncomputable def ridingK(i:D):= (s.toFinset ∩ barn o (qT i)).powerset.filter (fun j=> j.Nonempty)
noncomputable abbrev MotK:= Tool (ridingK o s F)
local notation "E"=> MotK o s F
lemma tightK(i:D)(x:↥(ridingK o s F i)): x.val⊆ s.toFinset ∧ x.val.Nonempty ∧ x.val⊆ barn o (qT i):=by
    obtain ⟨hv,hk⟩:=mem_filter.mp x.2; have h:=mem_powerset.mp hv; exact ⟨h.trans inter_subset_left,hk,h.trans inter_subset_right⟩
-- s.filter supports.C.Len.Compiler.Hole.
local notation "gΦ" i:arg=> s.filter (fun j=>j∈ (i:Finset I))
noncomputable def furtherK (bQ:ℝ): Patron.Rail c (ample N I) (D⊕E):=⟨Sum.elim F.addr (fun i:E=>⟨growsZ o (qT i.fst) i.snd.val,(F.addr i.fst).inv,(F.addr i.fst).alive, (F.addr i.1).part.trans subset_union_left⟩),Sum.elim F.warp (fun i:E=> fun j:Grid c=> banknote N o bQ ((Φ j) (gΦ i.snd.val) (withdraw N o bQ (F.warp i.1 j))))⟩
noncomputable def roofV : D⊕E→ Hat c:= Sum.elim F.addr (F.addr ∘ Sigma.fst)
local notation "K"=> furtherK o V H d s F t
local notation "Z"=> roofV o s F
local notation "mΦ" s:arg=> banknote N o t s
include H
variable (h: Wage.Tip N o (traceI I) F U t b v)(ht:0 < t)
include h ht
set_option maxHeartbeats 540000 in
lemma paneK (i:E)(X:Grid c): Well N o t q ((K).warp (Sum.inr i) X) ∧ Gated ((K).addr (Sum.inr i)).place ((K).warp (Sum.inr i) X) ∧ (vacR (Spine I) (Keys c N)).comp (withdraw N o t) ((K).warp (Sum.inr i) X)=0:=by
     let x:= F.warp i.1 X; let y:= L x; let F':=(Φ X) (gΦ i.snd.val); let Q:=R (F' y); have hx:Well N o t q x:=h.fits i.1 X; have hh:ValidPieces (Keys c N) q univ y:=hx.applies; let A:= qT i.fst; let Z':=i.snd.val; let J':=(gΦ Z'); have hk := viewingP s i.snd.val (tightK o s F i.fst i.snd).1; have hh':{j:I|j∈J'}.Nonempty:=by
          obtain ⟨j,hj⟩:=(tightK o s F i.fst i.snd).2.1; exact ⟨j,List.mem_toFinset.mp ((show J'.toFinset=Z' from hk).symm ▸ hj)⟩
     have hf:= briskU o V H d J' X ∅ y hh' hh; have hZ:L Q=F' y:=Cupola.home N o t ht _; let P':=(K).addr (Sum.inr i); have hp':P'.place=growsZ o A i.snd.val :=rfl; have hq:(vacR (Spine I) (Keys c N)) (L Q)=0:=Subtype.ext ((revive ..).trans ((congr_arg (pluck _ ∅) hZ).trans hf.2)) -- orientation
     refine ⟨⟨congr_arg _ hZ, hZ.symm ▸ hf.1⟩,?_,hq⟩
     change (light _ (R (F' y))) ∈ region (limits P'.place); rw [hh.wholeV,map_sum,map_sum,map_sum]; apply Subalgebra.sum_mem; intro j hj; let f:= Cupola.pick (Keys c N) q j y
     have hx(K':Finset (Spine I)):pluck (Keys c N) K' f=if K'=burst q j then pluck (Keys c N) (burst q j) y else 0:=by unfold f Cupola.pick; rw [many]; split; rw [show K'=_ from by assumption]; rfl
     have hy:Gated A x:= h.tilt.uses.role i.fst X
     by_cases ht:j.image o⊆ A; swap
     · have hq : pluck (Keys c N) (burst q j) y=0:=Cupola.confined N o t (burst q j) x A hy (fun hu=> ht ((held_pins o A j q).1 hu))
       have hf:f=0:=by apply pluckVisible; intro k; rw [hx,hq,map_zero,ite_self]
       change light _ (R (F' f))∈ _; rw [hf,map_zero,map_zero,map_zero]; exact Subalgebra.zero_mem _
     have hr : clad (limits A) f.val:=fun K'=>by
         change pluck (Keys c N) K' f∈_; rw [hx]; split; exact Cupola.pennied N o t _ x A hy; exact Subalgebra.zero_mem _
     let W:= Z'∪ j; have hm: Polite q W (F' f):=by
          have hv :Polite q (J'.toFinset ∪ j) (F' f):=pay_pieceU _ _ d J' (choseTuft ..); rw [show J'.toFinset=Z' from hk] at hv; exact hv
     have hW:W.image o ⊆ A:=by unfold W; rw [image_union]; apply union_subset _ ht; intro j hj; obtain ⟨p,hp,rfl⟩:=mem_image.mp hj; exact (inside ..).1 ((tightK o s F i.1 i.2).2.2 hp)
     have hxi:clad (limits P'.place) (F' f).val:=(hp'.symm ▸ (show clad (limits (growsZ o A i.snd.val)) (F' f).val from by have hQ:= cladU o V H d J' X f A hr; rw [show J'.toFinset= i.snd.val from hk] at hQ; exact hQ))
     change light _ (R (F' f)) ∈_; rw [bank_spent, show light _ (F' f)=_ from hm.exact.symm]; exact Ribbon.entitled N o t _ (burst q W) _ (hxi _) fun j hj=> ((show A ⊆ P'.place from subset_union_left) (hW (mem_image_of_mem _ (located (traceI I) W _ hj)))) -- `light` universe
lemma aliveK : Vital (K) (Z) U.threshold:=by
      constructor
      · rintro (i|i); · exact subset_refl _
        exact subset_union_left
      · rintro (i|i)<;> rfl
      · rintro (i|i); · exact h.tilt.uses.uses i
        intro U1 V1 hx hy; let t':= gΦ i.snd.val; let A:= qT i.fst; let T:= (K).addr (Sum.inr i); have hh:T.place = growsZ o A t'.toFinset:=by rw [show t'.toFinset= _ from viewingP s _ (tightK o s F i.1 i.2).1]; rfl
        have hz := Work.H03.reads_larger (show A⊆ T.place from subset_union_left) (h.tilt.uses.uses i.1) U1 V1 hx hy; change R ((Φ U1) t' (L (F.warp i.1 U1)))= R ((Φ V1) t' (L (F.warp i.1 V1))); rw [hz,readsU o V H d t' U1 V1 A (hh ▸ (show Agrees T.place U1 V1 from hx))]
      · rintro (i|i); · exact h.tilt.uses.reads i
        exact (R).toLinearMap.toContinuousLinearMap.measurable.comp (measurableU o V H d (gΦ i.snd.val) ((L).toLinearMap.toContinuousLinearMap.measurable.comp (h.tilt.uses.reads _)))
      · rintro (i|i) X; · exact h.tilt.uses.role i X
        exact (paneK o V H d s F h ht i X).2.1
      rintro (i|i); · exact h.tilt.pigment i
      intro X g; let x:= F.warp i.1 (Lattice.gauge g X); let y:= L x; let x':=F.warp i.1 X; let z:= L x'; have hY: R y=x:=(h.fits ..).spark; have hZ:L ((K).warp (.inr i) (Lattice.gauge g X))= _:= Cupola.home _ _ _ ht _ -- weak
      have hx: ValidPieces (Keys c N) q univ y:= (h.fits ..).applies; let g':= parcelColor N g I; have hh:R (g' y)=x':=by rw [show R (g' y)=_ from all_color N o t q g y hx, hY]; exact Subtype.ext (h.tilt.pigment i.1 _ g)
      have hv: z=g' y:= ((congr_arg L hh).symm).trans (Cupola.home N o t ht _)
      let p:=(gΦ i.snd.val); have he: Relation.ReflTransGen (fun _ _:ℝ=>False) 1 1:=.refl -- indentation
      have hh':ValidPieces (Keys c N) q univ ((Φ (Lattice.gauge g X)) p y):=by rw [← (show L _= _ from (show L ((K).warp (.inr i) (Lattice.gauge g X))=_ from Cupola.home _ _ _ ht _))]; exact (paneK o V H d s F h ht i _).1.applies -- implicit ?
      refine congr_arg Subtype.val (show sways (Lat.rotates μ₀ g) ((K).warp _ (Lattice.gauge g X))=(K).warp _ X from ?_); change sways (Lat.rotates μ₀ g) (R ((Φ (Lattice.gauge g X)) p y)) = R ((Φ X) p z); rw [show sways _ _= _ from (all_color N o t q g _ hh').symm, colorU o V H d p X g y, ← show z=parcelColor _ g I y from hv] -- obligations #
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.aliveK
