import YM.Clink.Nu
import YM.Clink.Night
import YM.Clink.Trench
/-! Aggregation of symbol and spin movements under actual observation mask. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J D E :Type}[Fintype I]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
namespace Basal
open QCD.Ruby Cove NormedSpace
open Massive.PCAC
variable {c f L:Side}{v t x δ α β κ ρ C C' ξ M B3 G3 σ B1 G1 a D_:ℝ}{P:BudgetPoint}{k n l m N:ℕ}
open Stitch
open Massive.PCAC.Oren
open Entr.Meridian
structure Surge (c:Side) where
    ray : Site c → Stall c 6
    halo : Site c → Grid c→EvenA c 6
namespace Surge
instance : Add (Surge c):=⟨fun i j=>⟨i.ray+j.ray,i.halo+j.halo⟩⟩
instance : SMul ℂ (Surge c):=⟨fun v i=>⟨v • i.ray,v • i.halo⟩⟩
instance : Zero (Surge c):=⟨⟨0,0⟩⟩
variable (S T: Surge c)(o:I→ Cover)(W:St c)(q:Set (Finset I))
local notation "u"=>wrap c ∘ o
local notation "K"=> Keys c 6
local notation "Ro"=> rootR (Spine I) K
noncomputable def eats (S:Surge c)(X:Massive.Density c 6)(p:Cover): Massive.Density c 6:=fun U=> S.ray (wrap _ p) U (X U)+ X U*(S.halo (wrap _ p) U).val
lemma sumE (X:Massive.Density c 6)(p:Cover): eats (S+T) X p=eats S X p+eats T X p:=by ext1 U; change (S.ray _ U (X U)+T.ray _ U (X U)) + (X U)* (_+_)= _+_+(_+_); rw [mul_add]; abel
lemma buyE (X:Massive.Density c 6)(p:Cover)(z:ℂ): eats (z • S) X p=z • eats S X p:=by ext1 U; change z • _+X U*(z • _)=z • (_+_); rw [mul_smul_comm,smul_add]; rfl
-- charter admits given or reel directly (permit mask). post budget.
structure Owns (S:Surge c)(o:I→ Cover)(P:BudgetPoint)(W:St c)(q:Set (Finset I))(σ v M ξ B₀ G₀:ℝ): Prop where
    rod (j:I): Suit (wrap c (o j)) P M (S.ray (wrap c (o j)))
    pays (k:I→ℂ): (∀ j:I, ‖k j‖≤ ξ) → ∃ (A B:Type)(_ : Countable A)(_ : Countable B)(R:Reel c 6 I A)(Z:Cape.Lure c 6 I B), CarryT (wrap c ∘ o) R Z P v σ B₀ G₀ q (deltaU (wrap c ∘ o) (fun j=>S.ray (wrap c (o j))) rod k (univ.toList) (rootR (Spine I) (Keys c 6) ∘ fun i=> nozzle c 6 (W i))+ vaultU (fun j=> k j • (S.halo (wrap c (o j)))))
variable (h: Owns S o P W q σ v M ξ B3 G3)
include h
open Cape
lemma wider0 (X:Set (Finset I)) (Y:Grid c→Patio (Keys c 6⊕Spine I))(R:Reel c 6 I D)(Z:Cape.Lure c 6 I E)(he:CarryT (wrap c ∘ o) R Z P v σ B3 G3 X Y)(hp:B3≤B1)(hg:G3≤G1) : CarryT (wrap c∘o) R Z P v σ B1 G1 X Y:=by
        obtain ⟨hz,hV,h,h'⟩:= he; obtain ⟨hf,hg',hr⟩:=hV; obtain ⟨f,h2,hF⟩:= hz.reserve; refine ⟨{ hz with reserve:= ⟨f,fun i=> budget_loosen (h2 i) hp,hF⟩ },⟨hf,hg',fun i=> budget_loosen (hr.1 i) hg,hr.2⟩,h,h'⟩ -- signature
-- extensional over delta when stretching constants: depends proofirrelevance on Bean, not same Suit amount
lemma swings (kp: M≤ C)(ht:B3≤B1)(hq:G3≤G1): Owns S o P W q σ v C ξ B1 G1:=by
       refine ⟨fun i=> Suit.beyond _ (h.rod i) kp,fun k h' =>?_⟩; obtain ⟨J,U,hU,hI,R,Z,hD⟩:=h.pays k h'; exact ⟨_,_,hU,hI,R,Z,wider0 S o W q h q _ R Z hD ht hq⟩ -- h rod proof irrelevance (rod bean)
lemma resizeA (z:ℂ)(k:ℝ)(Q1:ℝ)(ht:‖z‖≤k)(hk:k*M≤ Q1) (hv:0 ≤ C)(hη:k*C≤ ξ)(hK:0 ≤ M)(hQ:∀ i∈ q,i.card ≤1): Owns (z • S) o P W q σ v Q1 C B3 G3:=by
       have hP(j:I): Suit (u j) P Q1 ((z • S).ray (u j)):=by apply Suit.beyond _ (Suit.scaleF _ (h.rod j) z); exact (mul_le_mul_of_nonneg_right ht hK).trans hk
       refine ⟨hP,fun p' hh=>?_⟩; let F(k:I):=p' k*z; have hξ(j:I): ‖F j‖≤ξ:=by rw [show F j=p' j*z from rfl,norm_mul,mul_comm]; exact (mul_le_mul ht (hh j) (norm_nonneg _) ((norm_nonneg _).trans ht)).trans hη
       obtain ⟨A,B,hA,hB,R,X,hV⟩:=h.pays F hξ; refine ⟨_,_,hA,hB,R,X, ?_⟩
       let R':= Ro ∘ fun i=> nozzle c 6 (W i); let Y j:=S.ray (u j); let T j: Stall c 6:=(z • S).ray (u j)
       have he: deltaU u T hP p' univ.toList R'= deltaU u Y h.rod F univ.toList R':=by
              ext1 i; let p:=R' i; let V(k):=(hP k).bean i; let Z'(k):=(h.rod k).bean i; change actU _ V p' _ p-p=actU _ Z' F _ p-p; congr 1; generalize hv: (univ:Finset I).toList =list
              have hp(s:List I)(p:Patio (K⊕Spine I)): actU _ V p' s p=actU _ Z' F s p:=by
                   induction s generalizing p with
                   | nil=>rfl
                   | cons j l ih=>
                        rw[act_consU,act_consU,ih]; let y:= actU _ Z' F l p; have hv:(V j).twirl I y=z • (Z' j).twirl I y:=by apply pluckVisible; intro t; rw[Bean.onPiece,map_smul,Bean.onPiece]; rfl
                        rw [Bean.fate, Bean.fate,show (V j).twirl _ _=_ from hv,mul_smul_comm,smul_smul]
              exact hp _ _
       have hh: (fun j=>p' j • (z • S).halo (u j))=fun j=>F j • S.halo (u j):=funext fun j=>smul_smul ..
       change CarryT u R X P v σ B3 G3 q (deltaU u T hP p' univ.toList R'+ vaultU fun j=> p' j • (z • S).halo (u j)); rw [he, hh]; exact hV
lemma joins (hk:0≤σ)(hv:1 ≤ v) (hQ:∀ s∈q,s.card≤1)(hT:Owns T o P W q σ v C ξ B1 G1): Owns (S+T) o P W q σ v (M+C) ξ (B3+B1) (G3+G1):=by
       have he(j:I): Suit ((u) j) P (M+C) ((S+T).ray ((u) j)):= Suit.plus _ _ (h.rod j) (hT.rod j); refine ⟨he,fun k hp=>?_⟩
       obtain ⟨A,B,hA,hB,R,Z,hV⟩:= h.pays k hp; obtain ⟨U,O₁,hU,hO,R',Z',hV'⟩:=hT.pays k hp; let W' j:=k j • S.halo (u j); let f j:=k j • T.halo (u j); have hh:= CarryT.projection u (fun j=>S.ray (u j)) (fun j=>T.ray (u j)) (fun j=>(S+T).ray (u j)) k k k h.rod hT.rod he (fun i=> nozzle c 6 (W i)) (vaultU W') (vaultU f) q hQ univ.toList (nodup_toList _) (by simp) R R' Z Z' hV hV' hk hv (fun i U p=>smul_add ..) -- argument
       have hZ: vaultU (fun j=> k j • (S+T).halo ((u) j))= vaultU W'+vaultU f:=by
            ext1 i; unfold vaultU; rw [Pi.add_apply]; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _; change slipU j (k j • (_+_))=slipU j (_)+ slipU j (_); rw [smul_add,map_add]; rfl
       exact ⟨_,_,inferInstance,inferInstance,_,_,hZ.symm ▸ hh⟩ -- proof
end Surge
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.Surge.joins
#print axioms YM.MassiveQCD.Sample.Basal.Surge.resizeA
