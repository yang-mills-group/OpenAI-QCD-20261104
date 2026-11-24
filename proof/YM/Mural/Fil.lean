import YM.Mural.Cot
import YM.Mural.Scent
import YM.Mural.Voces
/-! # family companions of a shared shape. -/
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 900000
namespace YM.MassiveQCD.PaletteT
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon Lattice Wilson Lat RG
open scoped BigOperators Topology Classical ContDiff
variable {D E F I:Type} [Fintype I]{c f:Side} (N:ℕ)(p:Unit→Site c) (t:ℝ)
variable (g:Lat.Frame c) -- collision Frame P.Name! use Lat
open QCD.Finch Kites
local notation "M"=> ample N Unit
local notation "T'"=> Keys c N⊕ Spine Unit
variable (K:Delta I)
noncomputable def actC : EvenA c N→ₐ[ℂ]EvenA c N:= car (slots N g) (fun x h=> (exterior_parity _ _).trans (congr_arg _ h))
lemma act_at (x:EvenA c N): actC N g x= Patron.sways (Lat.rotates N g) x:=rfl
lemma inkdance (x:Tine c N Unit): dance Unit g N x = parcelColor N g Unit x:=rfl
variable {κ:Unit→Bool}
lemma commuteX (x:Tine c N Unit)(h:ValidPieces (Keys c N) κ univ x) : actC (ample N Unit) g (banknote N p t x)= banknote N p t (dance Unit g N x):=by rw [act_at,inkdance,all_color N p t κ g x h]
lemma renew (r b:ℝ) (X:Option I→EvenA c (ample N Unit))(h:Dealers N p t κ X)(hp:0<b): Dealers N p b κ (fun i=>changeBill N p r t b (X i)):=by
     have hm:=h.loose
     let T:= withdraw N p t; let x i:=T (X i); let y i:=turn Unit r (x i)
     change Dealers N p b κ (fun i=>banknote N p b (y i))
     refine Dealers.book ⟨cloak r _ _ _ hm.plain,fun i=>freight r _ _ (hm.finance _),fun i=>?_⟩ hp
     dsimp only [y]; rw [freeTurn,freeTurn r]; exact congr_arg _ (hm.bonds i)
lemma spinRev (r b:ℝ)(X Y:Option I→EvenA c (ample N Unit))(h:Dealers N p t κ X)(ht:Binds K (actC (ample N Unit) g) X Y)(hp:0<t):
       Binds K (actC (ample N Unit) g) (fun i=>changeBill N p r t b (X i)) (fun i=>changeBill N p r t b (Y i)):=fun i=>by rw [act_at,← changeColor N p r t b κ _ g (h.act i) hp, ←act_at,ht i]; unfold aggregate; rw [map_sum]; exact sum_congr rfl fun _ _=> map_smul ..
lemma emptyChange (r b:ℝ)(x:EvenA c (ample N Unit))(h:Mint N p t κ ∅ x)(hv:0<b) : Mint N p b κ ∅ (changeBill N p r t b x):=Mint.initiate ∅ hv _ (Plate.cloak r _ _ _ h.shows)
-- mint empty subalgebra
noncomputable def pocket (κ:Unit→Bool) (hv:0<t) : Subalgebra ℂ (EvenA c (ample N Unit)) where
 carrier:= {x|Mint N p t κ ∅ x}
 zero_mem' := Mint.none _
 one_mem' := Mint.oneV
 algebraMap_mem' c:= by
       rw [Algebra.algebraMap_eq_smul_one]; change Mint N p t κ ∅ (c • _); have he: Mint N p t κ ∅ 1:=Mint.oneV
       exact ⟨by unfold Function.comp; rw [map_smul,map_smul,map_one,map_one],by rw [map_smul]; exact he.shows.smooch _⟩
 mul_mem' := fun {x y} h g=> (by simpa using (Mint.boon (show Mint N p t κ ∅ x from h) (show Mint N p t κ ∅ y from g)))
 add_mem' := by intro x y hx hy; exact (Mint.gauge hv).mpr (by rw [map_add,(Mint.gauge hv).mp hx,(Mint.gauge hv).mp hy])
-- Mint and valid at neutral transitions.
lemma fresh_tariff (X:EvenA c (ample N Unit))(h:Mint N p t κ ∅ X) (hv:0<t): Dealers (P:=I) N p t κ (fun _=>X):=by
     refine ⟨fun _=>h.launch,h.shows,fun i=> h.launch.applies, fun i=> rfl⟩
lemma kindle (hv:0<t)(K:EvenA c N): Mint N p t κ ∅ (Apron.bearing Unit c N K):=by rw [← Apron.Grove.braces Unit p]; refine Mint.initiate _ hv _ ?_; unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
lemma talk (h:0<t) (x y:Option I→EvenA c (ample N Unit))(hx:Dealers N p t κ x)(hp:Binds K (actC M g) x y) :
    Binds K (dance Unit g N) (fun i=> withdraw N p t (x i)) (fun i=>withdraw N p t (y i)):=by
    intro i; let U:=withdraw N p t (x i); have hv:= hx.act i; have hG:banknote N p t (dance Unit g N U)=actC M g (x i):= (commuteX N p t g U hv.applies).symm.trans (congr_arg (actC M g) hv.spark); unfold aggregate
    rw [show dance Unit g N U=withdraw N p t (actC M g (x i)) from hG ▸ (Cupola.home N p t h _).symm, hp i]; unfold aggregate; rw [map_sum]; exact sum_congr rfl fun _ _=>map_smul ..
end YM.MassiveQCD.PaletteT
#print axioms YM.MassiveQCD.PaletteT.pocket
#print axioms YM.MassiveQCD.PaletteT.spinRev
#print axioms YM.MassiveQCD.PaletteT.renew
#print axioms YM.MassiveQCD.PaletteT.talk
