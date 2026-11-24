import YM.QCD.RP.Fare
import YM.QCD.Cove.Post
import YM.QCD.Tide.Pier
/-! Bounded Borel Grassmann pencils. Width/rates explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology ComplexOrder
variable {X Y Z E G A:Type*}

structure Stays [MeasurableSpace X] [MeasurableSpace E] [Norm E] (f:X→E):Prop where
    mes:Measurable f
    bounded:∃ C:ℝ, ∀ x,‖f x‖≤C
lemma Stays.intg [mx:MeasurableSpace X] [MeasurableSpace E][NormedAddCommGroup E][BorelSpace E][SecondCountableTopology E](μ:MeasureTheory.Measure X)[IsFiniteMeasure μ] {f:X→E}(h:Stays f):Integrable f μ:=by
      obtain ⟨C,hC⟩:=h.bounded; exact Integrable.of_bound h.mes.aestronglyMeasurable C (.of_forall hC)
lemma stays [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] [MeasurableSpace E][NormedAddCommGroup E][BorelSpace E]{f:X→E}(h:Continuous f):Stays f:=⟨h.measurable,h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
lemma Stays.travel [MeasurableSpace X][MeasurableSpace Y][MeasurableSpace E][Norm E] {p:X→Y}{f:Y→E}(h:Stays f)(hp:Measurable p): Stays (f ∘ p):= by obtain ⟨C,hC⟩:=h.bounded; exact ⟨h.mes.comp hp,C,fun x=> hC _⟩
lemma Stays.flows [MeasurableSpace X][MeasurableSpace Y][MeasurableSpace E][NormedAddCommGroup Y][ProperSpace Y][BorelSpace Y][NormedAddCommGroup E][BorelSpace E]{p:X→Y}{f:Y→E}(h:Stays p)(hp:Continuous f): Stays (f ∘ p):= by
      obtain ⟨C,hC⟩:=h.bounded
      obtain ⟨D,hD⟩:= ((isCompact_closedBall (0:Y) C).image hp.norm).bddAbove
      refine ⟨hp.measurable.comp h.mes,D,fun x=>hD ⟨p x,Metric.mem_closedBall.mpr (by simpa using hC x),rfl⟩⟩
lemma Stays.both [MeasurableSpace X][MeasurableSpace Y][MeasurableSpace E][NormedAddCommGroup Y][NormedAddCommGroup E]{p:X→Y}{f:X→E}(h:Stays p)(hp:Stays f): Stays (fun i=>(p i,f i)):= by
      obtain ⟨C,hC⟩:=h.bounded; obtain ⟨D,hD⟩:=hp.bounded; exact ⟨h.mes.prodMk hp.mes,D⊔C,fun i=> max_le ((hC i).trans (le_max_right ..)) ((hD i).trans (le_max_left ..))⟩
lemma Stays.mult [MeasurableSpace X][NormedRing Y][MeasurableSpace Y][ProperSpace Y][BorelSpace Y][SecondCountableTopology Y] {p f:X→Y}(h:Stays p)(hp:Stays f): Stays (p*f):= (h.both hp).flows continuous_mul
lemma Stays.acts [MeasurableSpace X][NormedField G][NormedAddCommGroup Y][NormedSpace G Y][MeasurableSpace G][MeasurableSpace Y][ProperSpace Y][BorelSpace Y][SecondCountableTopology Y][ProperSpace G][BorelSpace G][SecondCountableTopology G] {p:X→G}{f:X→Y}(h:Stays p)(hp:Stays f): Stays (fun i=> p i • f i):= (h.both hp).flows (continuous_fst.smul continuous_snd)
instance proper [Fintype A]:ProperSpace (Alg A) := FiniteDimensional.proper ℂ _
variable {n c f : Side} {F : ℕ} {C : Lat.Cut n F} {R : Cells.Cut n} {S P : Set (Site n)}
abbrev Stud (n:Side)(F:ℕ):= Grid n→Fields n F
abbrev inSlot (S : Set (Site n))(v:Fields n F): Prop:= ∃ u, v=pass (setDay S) u
abbrev Uses (S : Set (Site n))(x:Stud n F):Prop:= LocalOn S x∧ ∀ U,inSlot S (x U)
abbrev Neutral (x:Stud n F):Prop:=∀ k U,slots F k (x (gauge k U))=x U
noncomputable def foldsT (R : Cells.Cut n) (x : Stud n F): Stud n F:= fun U=> theta R (x (R.pullC su U))
lemma foldsPay (x:Stud n F)(h:Stays x): Stays (foldsT R x):= (h.travel (p:=R.pullC su) (Wilson.continuous_pull _ _|>.measurable)).flows (tilt_cont _)
noncomputable def coat (T:Tape n) (x: Stud n F): Stud n F:= fun U=> T.tape F (x U)
lemma coating (k:Tape n)(x:Stud n F)(h:Stays x):Stays (coat k x):= h.flows ((k.tape F).toLinearMap.continuous_of_finiteDimensional)
lemma floods (x:Stud n F)(h:Neutral x):Neutral (foldsT R x):=by
     intro k U; have he:= ContinuousMap.congr_fun (respects (R:=R) k (ContinuousMap.const _ (x (R.pullC su (gauge k U))))) U; unfold foldsT; change _= _ at he -- const LHS. actual θ.R
     change slots _ _ (theta R (x (pull _ _ (gauge k U))))=_
     refine Eq.trans he ?_; change theta R (slots _ _ (x (R.pullC su (gauge k U))))=_; change theta R (slots _ _ (x (pull _ _ (gauge k U))))=_; rw [face_rot]; exact congr_arg (theta R) (h (k ∘ R.reflect) _) -- after he mismatched
lemma coated (k:Tape n)(x:Stud n F)(h:Neutral x):Neutral (coat k x):= by intro K U; unfold coat; rw [← Tape.tape_slot,h]
lemma coatS (k:Tape n)(x:Stud n F)(h:Uses S x): Uses S (coat k x):=by
      refine ⟨fun U V e=> congr_arg (k.tape _) (h.1 U V e),fun U=>?_⟩; obtain ⟨p,hp⟩:= h.2 U
      obtain ⟨v,-,-,hv⟩:= rolling_maps k (x:=ContinuousMap.const _ (pass (setDay S) p)) ⟨fun _=>p,continuous_const,(fun _ _ _=> rfl),(fun _=> rfl)⟩; exact ⟨v U,(congr_arg (k.tape F) hp).trans (hv U)⟩
lemma foldsS (x:Stud n F)(h:Uses S x)(hz:Set.MapsTo R.reflect S P): Uses P (foldsT R x):=by
      refine ⟨fun U V e=> congr_arg (theta _) (h.1 _ _ (sees _ _ _ _ hz e)),fun U=>?_⟩; obtain ⟨p,hp⟩:=h.2 (R.pullC su U); obtain ⟨v,-,-,hv⟩:= reflects_map (x:=ContinuousMap.const _ (pass (setDay S) p)) ⟨fun _=>p,continuous_const,(fun _ _ _=> rfl),(fun _=> rfl)⟩ hz; exact ⟨v U,(congr_arg (theta R) hp).trans (hv U)⟩
end YM.QCD.Tide
