import YM.Lobo.Wafer
import YM.Lobo.Camel
set_option maxHeartbeats 680000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
variable {d:ℕ}(a b:Axis)(f:Flavor 6)(w:Bool) (i j k:Tri) -- remove
noncomputable def dimiL (j q: Multi d)(h:spinWeight j+spinWeight q≤d):Spike→ₗ[ℂ]Label d where
     toFun M:= solstice f M j q h
     map_add' x z:=Subtype.ext (by change bilinear f f (x+z) _ _= bilinear _ _ x _ _+ bilinear _ _ z _ _; simp only [UV.bilinear, Matrix.add_apply,add_smul,sum_add_distrib, TensorProduct.tmul_add])
     map_smul' a x:=Subtype.ext (Oriole.nourish ..)
structure Lone (b:IceT)(x:Label d) :Prop where
  cov : ∀ K:EuPin,∀ p:PClan,∀ i:Tri,∀ t:ℝ,(b.elim K p).coord=Thr i t→putH (K,p) d x=x
  q : x∈Qa d
structure Brook (b:IceT)(x:Tri→ Label d):Prop where
  cov:∀ K:EuPin,∀ p:PClan,∀ i:Tri,∀ t:ℝ,(b.elim K p).coord=Thr i t →∀ j,putH (K,p) d (x j)=wing i t x j
  q:∀ i,x i∈ Qa d
structure BraceP (b:IceT)(x:Tri→Tri→ Label d) :Prop where
  cov:∀ K:EuPin,∀ p:PClan,∀ i:Tri,∀ t:ℝ,(b.elim K p).coord=Thr i t →∀ j k, putH (K,p) d (x j k)= wing i t (fun a=>wing i t (x a) k) j
  q:∀ i j,x i j∈ Qa d
-- directives pick
lemma oneH (s:RawSym) : Lone none (s.unit 8):=by
      constructor
      · intro K p i t h; apply Subtype.ext; change carr (K,p) _ _ = _; rw [s.unitActs]; exact (by unfold unit; exact (carrying K p _ _).trans (congr_arg (tmul ℂ 1) (map_one _))) -- order
      change Quiet (s.unit 8).val; rw[s.unitActs]; exact plainQ (1:GPol)
lemma crestT(b b':Bool): BraceP none (nodes b b'):=⟨fun K p i t h a z=> racoon K p a z i t b b' h, fun i j=>plainQ _⟩
variable (M:Spike)
local notation "A" => Label 8
local notation "Q" =>Qa 8
local notation "U"=> (0:Multi 8)
noncomputable def swamp (f:Flavor 6)(i:Axis)(h:Bool):Spike →ₗ[ℂ] Label 8:= if h then dimiL f (UV.first i) U (by rw [juicy,cost_root]) else dimiL f U (UV.first i) (by rw[juicy,cost_root])
noncomputable def gulf (f:Flavor 6): Spike →ₗ[ℂ] Label 8:= dimiL f U U (by rw [cost_root]; decide)
lemma crestS : gulf f M ∈ Q:= flora f M U U (by rw [cost_root]; decide)
lemma crestP : swamp f a w M∈ Q:=by unfold swamp; split_ifs; exact flora f M (UV.first a) U (by rw[juicy,cost_root]); exact flora f M U (UV.first a) (by rw[juicy,cost_root])
variable (K:EuPin)(p:PClan)(t:ℝ)(he:(p f).coord=Thr k t)
lemma simplP: Euv p f f M=conjug (p f) M:=(mul_assoc ..).symm
lemma knob: putH (K,p) _ (gulf f M)= gulf f (conjug (p f) M):= Subtype.ext ((sig0 f f K p M 8).trans (congr_arg (fun M=> bilinear f f M U U) (simplP f M p))) -- order
include he
lemma wingM : putH (K,p) _ (swamp f a w M)=palm k t (fun b=>swamp f b w (conjug (p f) M)) a:=by
    apply Subtype.ext
    cases w
    · change carr (K,p) _ (bilinear f f M U (UV.first a))=_; rw[sigA,simplP]; unfold palm; rw[AddSubmonoidClass.coe_finsetSum]; refine sum_congr rfl fun i _=>?_ ; rw[he]; rfl
    change carr (K,p) _ (bilinear f f M (UV.first a) U)=_; rw[sigP,simplP]; unfold palm; rw[AddSubmonoidClass.coe_finsetSum]; exact sum_congr rfl fun i _=>by rw[he]; rfl
omit he
variable (u v:Bool)
local notation "X"=> flat (none,u,v)
local notation "Y" => fun i:Tri=> flat (some i,u,v)
lemma wing_map {T₀ Z:Type}[AddCommGroup T₀][Module ℂ T₀][AddCommGroup Z][Module ℂ Z] (i j:Tri)(t:ℝ)(p:Tri→T₀)(F:T₀→ₗ[ℂ]Z): F (wing i t p j)=wing i t (fun i=> F (p i)) j:=by unfold wing; rw[map_sum]; exact sum_congr rfl fun z _=>map_smul ..
lemma twirp : Lone (some f) (gulf f X):= by refine ⟨fun K p i t h=>?_, crestS ..⟩; rw [knob,azure i t (p f) h]
lemma twirl : Brook (some f) (fun i:Tri=> gulf f ((Y) i)):= by refine ⟨fun K p i t h j=>?_, fun _=>crestS ..⟩; dsimp only; rw [knob,chrome i j t (p f) h]; exact wing_map (T₀:=Spike) (Z:=Label 8) i j t _ (gulf f)
lemma spinT : Lone (some f) (swamp f timeAxis w X):=by refine ⟨fun K p i t h=>?_,crestP ..⟩; rw [wingM timeAxis f w i X K p t h,lastB,azure i t (p f) h]
lemma spanT : Brook (some f) (fun i=> swamp f (lieu i) w X):=by refine ⟨fun K p i t h j=>?_,fun _=>crestP ..⟩; rw [wingM (lieu j) f w i X K p t h,hat,azure i t (p f) h]; rfl
lemma spunS : Brook (some f) (fun i:Tri=>swamp f timeAxis w ((Y) i)):=by refine ⟨fun K p i t h j=>?_,fun _=>crestP ..⟩; dsimp only; rw [wingM timeAxis f w i _ K p t h,lastB,chrome i j t (p f) h]; exact wing_map (T₀:=Spike) (Z:=Label 8) i j t _ (swamp f timeAxis w)
lemma spearT : BraceP (some f) (fun i j:Tri=> swamp f (lieu i) w ((Y) j)):=by
     refine ⟨fun K p i t h j k=>?_,fun i j=>crestP ..⟩; dsimp only; rw [wingM (lieu j) f w i _ K p t h,chrome i k t (p f) h,hat]; apply congr_arg (fun f:Tri→A=> wing i t f j); funext z; exact wing_map (T₀:=Spike) (Z:=Label 8) i k t (fun j=>flat (some j,u,v)) (swamp f (lieu z) w)
end YM.Lobo
#print axioms YM.Lobo.spearT
#print axioms YM.Lobo.twirp
#print axioms YM.Lobo.twirl
#print axioms YM.Lobo.spinT
#print axioms YM.Lobo.spunS
#print axioms YM.Lobo.spanT
#print axioms YM.Lobo.oneH
#print axioms YM.Lobo.crestT
