import YM.QCD.Villa.Reel

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
local notation "V'"=> prism T τ
open Art
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
-- common combining
variable {s:Signed}{b:Site c}{π:R.activities.Moves s (S.ratio.embed b)}{Ω:Equiv.Perm ι}{K: EvenA c N→+*EvenA c N}{Z:Site c→su.El} {κ:Type} {Ω':Equiv.Perm κ}{A:Fleet H κ N}
lemma jointly (h:Y.Marches π Ω K)(ht:A.Marches π Ω' K) : (Fleet.united Y A).Marches π (Equiv.sumCongr Ω Ω') K:=by
    refine ⟨h.cont,?_,?_,?_,?_,?_⟩
    all_goals rintro (i|i)
    all_goals first | exact h.days i|exact ht.days i|exact h.paths i|exact ht.paths i|exact h.glasses i|exact ht.glasses i|exact h.turns i|exact ht.turns i|skip
    all_goals rintro (j|j) <;> first | exact h.groups i j | exact ht.groups i j| exact Iff.rfl
lemma graft (h:Y.sings Z K)(hp:A.sings Z K): (Fleet.united Y A).sings Z K:=by constructor; exact h.cont; rintro (i|i); exact h.verse i; exact hp.verse i
lemma voice (h:Y.speaking)(hp:A.speaking): (Fleet.united Y A).speaking:=by rintro (i|i); exact h i; exact hp i
end YM.QCD.Loom.Fleet

namespace YM.QCD.Villa
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Cove Leaf Lat Creek Loom
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass Sway OrbitG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {Y:StepData c f} {η p h z a a' t v u u' q:ℝ} {D E J:Type}[Countable E][Countable J][Fintype D]
variable {T : Tube su Y} {W' :ℕ→Atom su 2} {P':Plan k} {L:Side}
variable (H:Cash W τ μ L Q o C T (trimP T R δ β b))
open AnalyticBridge.GaussianFieldAlignment Locations Channels PhysicalNext.Repeat.Turn Next.Fluctuations Next.SectorChange
lemma halo_image (d:ℕ)(p:Signed)(u:Site c)(S: Support c): halo d (S.image (affine p u))=(halo d S).image (affine p u):= Push.Local.halo_map (StepData.sendSites p u) (Push.Local.turn_sep p u) _ _ -- maybe orientation
lemma parent_image (X:Support f)(p:Signed)(u:Site c): (X.image Y.ratio.parent).image (affine p u)=(X.image (affine p (Y.ratio.embed u))).image Y.ratio.parent:=by
   rw [image_image,image_image]; refine image_congr fun x _=>?_ ; exact Eq.symm (Locations.parent_map p u x)
lemma presenceP (X: Grid c): gauge (fun _=> (1:su.El)) X=X:=by funext i; simp [Lattice.gauge]
lemma permanence (g:OrbitG (Modes f N)) (X:Rise f N E J) (t:ℝ) (h:∀ i U,g.passL (X.main i U)=X.main i U)(ht:∀ i U,g.passL (X.plug i U)=X.plug i U)(U:Grid f): Parade U U g X (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) t:=by refine ⟨?_,?_,?_,?_,?_, fun i=>h i U,fun i=>ht i U⟩ <;> simp
open PhysicalNext.Repeat.Pane in
lemma mac_m (s:Signed)(x:Site c) : ∃ π:(trimP T R δ β b).activities.Moves s (Y.ratio.embed x),∀ y:Site f,π.kp (mac y)=mac (affine s (Y.ratio.embed x) y):=by
  let v:=Y.ratio.embed x; let u := Equiv.prodCongr (StepData.sendSites s v) (Equiv.refl ℕ); let e:=keys f; let p: Equiv.Perm ℕ:= (e.trans u).trans e.symm
  have he (w:Site f): p (mac w)=mac (affine s v w):= e.injective (by simp [p,e,u,mac]; rfl)
  have hy i : abscissas f (p i)=affine s v (abscissas f i) := congr_arg Prod.fst (show e (p i)=u (e i) from e.apply_symm_apply _)
  have hv i : ({abscissas f (p i)}:Support f)= image (affine s v) {abscissas f i}:= by simp [hy]
  refine ⟨⟨p,p,hy,hv,hv,hv, fun _ _=> Iff.rfl, fun _ _=>rfl, fun i U=>?_⟩,he⟩
  dsimp only [trimP,pearl]; rw [hy,← he, ← Work.H03.flags_send (G:=su) s v R.threshold U]; simp only [Equiv.apply_eq_iff_eq]
  have hh : Injective (affine s v):= (StepData.sendSites s v).injective
  apply if_congr _ rfl rfl
  apply and_congr Iff.rfl
  exact ⟨fun ha=> by obtain ⟨z,hz,hQ⟩:= mem_image.mp ha; exact hh hQ ▸ hz,fun h=> mem_image_of_mem _ h⟩
end YM.QCD.Villa
