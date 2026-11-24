import YM.Sunda.Spot
import YM.Sunda.Meld
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Poised Massive.Poised.Display Massive.Poised.Stative Module Finset Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Lobo
variable (k i j:Tri)(t:ℝ)(f g:Flavor 6)(p:RawSym)
variable {d:ℕ} (M:Spike)(P Q:Multi d)
noncomputable def doses (ht:spinWeight P+spinWeight Q≤d):Spike→ₗ[ℂ] Label d where
    toFun M:= satin f g P Q M ht
    map_add' x y:=Subtype.ext (by change bilinear f g (x+y) _ _=bilinear _ _ x _ _ + bilinear _ _ y _ _; simp only [UV.bilinear, Matrix.add_apply,add_smul,sum_add_distrib,TensorProduct.tmul_add])
    map_smul' a x:=Subtype.ext (Oriole.nourish ..)
local notation "U"=>(0:Multi d)
noncomputable def limn (d:ℕ): Label d →ₗ[ℂ] (ℝ→Label d):= LinearMap.pi fun t=> (p.pin d (pathW k t)).toLinearMap -- RawSym.pin type differs
local notation "L"=> limn k p d
lemma leadings (x:Label d) : L x t= putH (pathW k t,plainPicture (pathW k t)) d x:=Subtype.ext ((p.pinActs d _ _).trans (spine_pin ..).symm)
include p
noncomputable abbrev rind (f g:Flavor 6)(hd:spinWeight (0:Multi d)+spinWeight (0:Multi d) ≤ d): Spike→ₗ[ℂ] Label d:= doses f g U U hd
variable (hz:spinWeight (0:Multi d)+spinWeight (0:Multi d) ≤ d)
local notation "Z"=>rind f g hz
lemma tides : L (Z M) t=Z (conjug (pathW k t) M):=by
     rw[leadings]; let G:=pathW k t; have he:Euv (plainPicture G) f g M=conjug G M:=(mul_assoc ..).symm; apply Subtype.ext; change carr (G,plainPicture G) d (bilinear f g M U U)=_; rw [sig0,he]; rfl
variable (u v:Bool)
local notation "X"=> flat (none,u,v)
lemma lineM : L (Z M)∈ Uno (Label d):=by
      let S:= (Uno (Label d)).comap (L ∘ₗ Z)
      have ht (u v:Bool): S.carrier.Mem (flat (none,u,v)):=by
             change L (Z _)∈ Uno (Label d); rw [funext (show ∀ t:ℝ,L (Z (flat (none,u,v))) t=Z (flat (none,u,v)) from fun t=> by rw[tides,azure k t _ ((treks k).2.2 t)])]; exact univoc _
      have hv(i:Tri)(u v:Bool): flat (some i,u,v)∈ S:=by
             change L (Z _)∈ Uno (Label d); have h(t:ℝ): L (Z (flat (some i,u,v))) t= Z (wing k t (fun i=>flat (some i,u,v)) i):=by rw[tides, chrome k i t _ ((treks k).2.2 t)]
             refine Eq.subst (motive:=fun g:ℝ→Label d=>g∈Uno (Label d)) (funext h).symm ?_; exact uni_map (E:=Spike) (Y:=Label d) (chord k i _) Z
      have he: Submodule.span ℂ (Set.range flat) ≤ S:= Submodule.span_le.mpr (by rintro t ⟨⟨w,x,y⟩,rfl⟩; cases w; exact ht ..; exact hv ..); rw [spans] at he; exact he (show M∈ (⊤: Submodule ℂ Spike) from Submodule.mem_top)
-- classify p q for low
omit p
lemma reap (ht:d<8)(h:spinWeight P+spinWeight Q≤d) : P=0∧Q=0:=by
      constructor; · apply Oriole.ground; unfold spinWeight at *; omega
      apply Oriole.ground; unfold spinWeight at *; omega
include p
lemma born : L (p.unit d) t=p.unit d:=by rw[leadings]; apply Subtype.ext; change carr _ d (p.unit d).val=(p.unit d).val; rw [p.unitActs]; unfold unit; rw [carrying,map_one]
lemma birthed : L (p.unit d)∈ Uno (Label d):=by rw[funext (show ∀ t:ℝ,L (p.unit d) t= p.unit d from fun t=>born k t p)]; exact univoc _
lemma came (ht:d<8)(G:Labels.Label su (d/2)): L (dowry G)∈ Uno (Label d):=by
      obtain ⟨z,hz⟩:= unitMine (show d/2< 4 by omega) G; rw [show dowry (d:=d) G=z • p.unit d from ?_, map_smul]; exact Submodule.smul_mem _ _ (birthed k p)
      rw [hz]; apply Subtype.ext; rw [Submodule.coe_smul,p.unitActs]; exact (plain (d:=d)).map_smul z (1:GPol)
lemma living (ht:d<8)(x:Label d): L x∈ Uno (Label d):=by
      refine purse x ht.le ((Uno (Label d)).comap L) (came k p ht) (fun a b P Q he M=>?_); obtain ⟨rfl,rfl⟩:= reap P Q ht he; exact lineM k a b p M he
local notation "A"=>limn k p 8
local notation "C"=> Label 8
lemma holler (x y:Bool): A (nodes x y i j)∈ Tres C:=by
     have h(t:ℝ): A (nodes x y i j) t=wing k t (fun a=>wing k t (nodes x y a) j) i:=by rw[leadings]; exact (crestT x y).cov _ _ k t ((treks k).2.2 t) i j
     refine Eq.subst (motive:=fun f:ℝ→C=> f∈ Tres C) (funext h).symm ?_; exact anthem k i (fun a t=>wing k t (nodes x y a) j) (fun i=> chord k j _)
omit p
local notation "U₁"=> (0:Multi 8)
noncomputable def dunes(a b:Flavor 6)(i:Axis)(y:Bool):Spike →ₗ[ℂ] Label 8:= if y then doses a b (UV.first i) U₁ (by rw[juicy,cost_root]) else doses a b U₁ (UV.first i) (by rw[juicy,cost_root])
local notation "D" i:arg=> dunes f g i u
variable (a:Axis)
include p
lemma dunesA : A (dunes f g a u M) t=palm k t (fun b=> dunes f g b u (conjug (pathW k t) M)) a:=by
     rw [leadings]; apply Subtype.ext; let G:=pathW k t; have he:Euv (plainPicture G) f g M=conjug G M:=(mul_assoc ..).symm; cases u
     · change carr (G,plainPicture G) 8 (bilinear f g M U₁ (UV.first a))=_; rw [sigA,he]; unfold palm; rw [AddSubmonoidClass.coe_finsetSum]; exact sum_congr rfl fun i _=> congr_arg₂ (fun (z:ℂ) (x:Pol 8)=> z • x) (congr_arg Complex.ofReal (congr_arg (fun p:Ortho=>p.val i a) ((treks k).2.2 t))) rfl
     change carr (G,plainPicture G) 8 (bilinear f g M (UV.first a) U₁)=_; rw [sigP,he]; unfold palm; rw [AddSubmonoidClass.coe_finsetSum]; exact sum_congr rfl fun i _=> congr_arg₂ (fun (z:ℂ) (x:Pol 8)=> z • x) (congr_arg Complex.ofReal (congr_arg (fun p:Ortho=> p.val i a) ((treks k).2.2 t))) rfl
variable (w:Bool)
lemma fanq (p':GammaRow): A (dunes f g a u (flat p'))∈ Tres C:=by
     have h0 : (fun t:ℝ=>conjug (pathW k t) (flat p'))∈Uno Spike:=by
           rcases p' with ⟨i,u,v⟩; rcases i with _|i; · refine Eq.subst (motive:=fun f:ℝ→Spike=>f∈Uno Spike) (funext (show ∀t:ℝ,conjug (pathW k t) (flat (none,u,v))= flat (none,u,v) from fun t=> azure k t _ ((treks k).2.2 t) u v)).symm (univoc _)
           refine Eq.subst (motive:=fun f:ℝ→Spike=>f∈Uno Spike) (funext (show ∀ t:ℝ,conjug (pathW k t) (flat (some i,u,v))= wing k t (fun i=>flat (some i,u,v)) i from fun t=> chrome k i t _ ((treks k).2.2 t) u v)).symm ?_; exact chord ..
     rcases Fin.eq_castSucc_or_eq_last a with ⟨i,rfl⟩|rfl
     · let W(j:Tri)(t:ℝ): Label 8:=dunes f g (lieu j) u (conjug (pathW k t) (flat p')); rw [funext (show ∀ t:ℝ,A (dunes f g (lieu i) u (flat p')) t= wing k t (fun i=> W i t) i from fun t=>by rw [dunesA,hat]; rfl)]; exact anthem k i W (fun i=>uni_map h0 _)
     rw [funext (show ∀ t:ℝ,A (dunes f g timeAxis u (flat p')) t=dunes f g timeAxis u (conjug (pathW k t) (flat p')) from fun t=>by rw[dunesA,lastB])]; exact upt C (uni_map h0 _)
lemma bigot(M:Spike)(h:spinWeight P+spinWeight Q≤d): (∃ h: d=8,True) → L (doses f g P Q h M)∈Tres (Label d):=by
     rintro ⟨rfl,-⟩; have he(i:Axis)(b:Bool):A (dunes f g i b M)∈Tres C:= harvest ((Tres C).comap _) (dunes f g i b) (fun p'=>fanq ..) _ -- inspect
     rcases (twoL P Q h) with ⟨rfl,rfl⟩| ⟨j,rfl,rfl⟩|⟨j,rfl,rfl⟩; exact upt C (lineM k f g p M h); exact he _ true; exact he _ false
lemma breaths(x:Label 8) : A x∈Tres C:=by
     let S:=(Tres C).comap A; have h:∀ a b c d:Axis, GG a b c d∈ S:= shops S (fun w u i j=> holler k i j p w u); exact purse x le_rfl S (fun i=>ceo S p i (upt _ (birthed ..)) h) (fun a b P Q h M=>bigot k a b p P Q M h ⟨rfl,trivial⟩)
end YM.Sunda
#print axioms YM.Sunda.living
#print axioms YM.Sunda.breaths
