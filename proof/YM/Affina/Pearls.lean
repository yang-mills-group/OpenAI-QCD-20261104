import YM.Affina.Fit
import YM.Plateau.Alf
import YM.Sprig.Moon
set_option autoImplicit false
noncomputable section
namespace YM.Sprig
open Function Filter Set MeasureTheory QCD.Sway
open Massive QCD QCD.Lat QCD.Grass Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open YM.Fir Massive.Fir Choir Pollens HarmonyF YM.Intag.Sprig YM.Intag.Sprig.Canopy Chloe
open Poised Plans Plans.Stamp Poised.Stative Finset
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}
variable (p q:Flavor 6)(g:Bool)
open Massive.Oriole Compass Submodule Massive.PCAC.Readout YM.MassiveCompletion SixFit
variable {J8:Label 8→ₗ[ℂ]Label 8}{J6:Label 6→ₗ[ℂ] Label 6}
variable {τ:ℝ} (u:Flavor 6→ℝ)(b:Flavor 6→Flavor 6→Bool→ℝ)
open MassFields Signals
variable (T:Pollens P Q)
noncomputable def MassM : MassFields:=⟨fun i j M=>UV.mesonCode _ i j M (by decide),fun i j M=>UV.mesonCode _ i j M (by decide),fun _ _ _=>rfl,fun _ _ _=>rfl⟩
local notation "s"=> charter u b τ
structure Apollo (Q:Choir)(p q:Flavor 6)(g:Bool)(c:ℂ): Prop where
     nonzero : ∀ a:Axis,axisP p q g Q a≠0
     other : lever p q g Q≠0
     room : lever p q g Q∈ Q.level 6
     divers : ∑ a:Axis,Q.arc a (axisP p q g Q a)=c • lever p q g Q
-- pairs compass.M vector/scalar
structure Arbit (S:Signals) (Q:Choir): Prop where
   realA (i j:Flavor 6): S.axial i j=S.axial j i
   realB (i j:Flavor 6): S.polar i j= -(S.polar j i)
   power (p q:Flavor 6) (h:p≠q): Apollo Q p q true (S.axial p q:ℂ) ∧ Apollo Q p q false (S.polar p q:ℂ)
variable (S: Signals)
variable (H: Q.Domestic)
variable {F6: UV.Free.Symbol 6≃ₗ[ℂ](Q.level 6)}(hf6:Prose F6 T)
variable (hT:∀ p q g,p≠q → (∀ i:Axis, Q.arc i (axisP p q g Q i) = Q.focus MassFields.isotropic 8 (stereo p q i (claw g i))))
include b u
variable (hU:∀ p q g,p≠q→ Honors Q p q g u (1/100*τ) (b p q g:ℂ))(hC:∀ i j k,b i j k=if k then b j i k else -(b j i k))
include hC hf6 hU H hT
lemma backs : Arbit (charter u b τ) Q:=by
     have h (i j:Flavor 6)(k:Bool)(hi:i ≠ j): Apollo Q i j k (b i j k:ℂ):=by
        obtain ⟨J,hJ⟩:=blunt i j k false 6; have hh:= hU i j k hi; exact ⟨torch T i j k hJ hf6 H hi,hh.nonzero,hh.room,(bodies _ _ _ (hT i j k hi)).trans hh.stars⟩
     exact ⟨fun i j=> hC i j true,fun i j=>hC i j false,fun i j hi=>⟨h _ _ _ hi,h _ _ _ hi⟩⟩
omit hC hf6 hU H hT b u
variable (Φ:EuPin→* (Q.W≃ₗ[ℂ]Q.W))(K:Ortho.Skew→ Q.W→ₗ[ℂ] Q.W)
local notation "Aq"=> equip T Φ K
variable (hX:Arbit S Q)(hM:S.Masses)
include hX hM
-- Exact post identity.Certificate needs rotated verified later.
lemma destiny (hv:∀ p q g,p≠q→ properVector (Aq) (axisP p q g Q))(hh:∀ p q g,p≠q→ properScalar (Aq) (lever p q g Q)): S.PCAC (Aq) MassM:=by
     let F:=equip T Φ K; refine ⟨hX.realA,hX.realB,fun i j h=>?_⟩
     obtain ⟨A,B⟩:=hX.power i j h
     have h1: MassM.axial F i j=axisP i j true Q:=rfl
     have h2: MassM.polar F i j=axisP i j false Q:=by ext a; change _= Q.focus _ _ (mesonCode _ _ _ (claw false a) _); rw [show claw false a=Lat.gamma a from mul_one (Lat.gamma a)]; rfl
     have h3: MassM.pseudo F i j=lever i j true Q:=rfl; have h4:MassM.scalar F i j=lever i j false Q:=rfl
     have hA: divergence F (MassM.axial F i j)=(S.axial i j:ℂ) • MassM.pseudo F i j:=A.divers
     have hV: divergence F (MassM.polar F i j)=(S.polar i j:ℂ) • MassM.scalar F i j:= by rw[h2]; exact B.divers
     have hp:= (add_pos (hM.positive i) (hM.positive j)).ne'
     have hd:= sub_ne_zero.mpr (hM.distinct.ne h)
     refine ⟨A.nonzero,?_,A.other,B.other,A.room,B.room,hv _ _ true h,?_,hh _ _ true h,hh _ _ false h,hA,hV,?_,?_⟩ -- VS field.V equality transport
     · intro a; change MassM.polar F i j a≠0; rw[h2]; exact B.nonzero a
     · change properVector F _; rw[h2]; exact hv i j false h
     · change divergence F _=_; rw [hA,Signals.renP,smul_smul,← Complex.ofReal_mul,show (S.bMass i+S.bMass j)*(S.axial i j/(S.bMass i+S.bMass j))=S.axial i j from by field_simp]
     · change divergence F _=_; rw[hV,Signals.renS,smul_smul,← Complex.ofReal_mul,show (S.bMass i-S.bMass j)*(S.polar i j/(S.bMass i-S.bMass j))=S.polar i j from by field_simp]
end YM.Sprig
#print axioms YM.Sprig.destiny
#print axioms YM.Sprig.backs
