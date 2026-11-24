import YM.Sprig.Eyre
/-! Actual purchased intermediate point exposures with linear equivariance on all components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator
variable {S:Scheme}{R:Side}{i j ℓ k p N:ℕ}{c:Side}{D d:ℕ}(A:Massive.Run S N R 6)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas
open UV
variable (V:Vista (S.side R i) D)(Ξ:RawSym)(Θ:TaperHol)
variable (hA:A.Actual) (h:i ≤ N)(ht:j≤ i)
local notation "Φ"=> (lung V)
local notation "Sn"=>S.side R
open Massive.Cylinder
-- linear syntax.
lemma readingO (X:Cover→Insertion (S.side R i) 6)(j:ℕ): tentT A none X j 0=(relay A j (X 0 *densityW A i)):=by
    unfold tentT report visitor; rw [smul_zero]; rfl
noncomputable def cereal (j:ℕ)(d:ℕ):Label d →ₗ[ℂ] Insertion (S.side R j) 6 where
    toFun x := relay A j (lung V d x 0 * densityW A i)
    map_add' x y:=by rw[map_add,Pi.add_apply,add_mul, map_add] -- add? fn inst
    map_smul' t x:=by rw [map_smul, Pi.smul_apply, smul_mul_assoc, map_smul]; rfl
-- true point calibration.Mirror.Really.AllSpots.
variable (L:Bore d) {W:Market S R d}(hf:Rubric Ξ L)(hW:Wager A Θ L W j)
noncomputable abbrev Attest (j:ℕ)(x y:Label d):Prop:= Tally Θ 0 y (A.density j) (cereal A V j d x)
local notation "π"=>Attest A V Θ
lemma witnesses (x y:Label d)(p:ℂ)(he:Attest A V Θ j x y):Attest A V Θ j (p • x) (p • y):=by
     let F:= foil (A.density j); let g:= cereal A V j d x
     unfold Attest; rw [map_smul]; refine ⟨he.unit,?_⟩; change Beacon.ActionTest Θ 0 (F ⇑(p • g)) _; rw [show F ⇑(p • g)=p • F g from funext fun i=> mul_smul_comm p (Ring.inverse ((A.density j) i)) (g i)]; exact Orientation.acting Θ 0 d (F g) y.val he.sees p
lemma brights (x y u v:Label d)(h:Attest A V Θ j x y)(hp:Attest A V Θ j u v):Attest A V Θ j (x+u) (y+v):=by
    unfold Attest; let F:= foil (A.density j); let T:=cereal A V j d; rw [map_add]; refine ⟨h.unit,?_⟩; change Beacon.ActionTest Θ 0 (F ⇑(T x+T u)) _; rw [show F ⇑(T x+T u)=F (T x)+ F (T u) from funext fun i=>mul_add ..]; exact Orientation.actsPlus Θ 0 d _ _ y.val v.val h.sees hp.sees
variable {Vb: YM.Source.Hol su}(P: Lining.Temper.Collage.Exhibit Vb)(Qv:∀ d,PatchMix d)(εr:ℝ)(base:ℕ→ℕ)
lemma smut(X:Glyph D)(w: Label X.width)(hp: TicketZ A P Θ V εr base Qv none X w): Attest A V Θ (base X.width) X.material ((tokenP X V:ℂ) • w):=by
     let t:ℂ:=tokenP X V
     let B:=base X.width; let f:= relay A B (Vista.spire X V 0*densityW A i); let F:= foil (A.density B); have he:= hp.harvest; rw[readingO] at he
     unfold Attest; rw [show cereal A V B X.width X.material = t • f from ?_]; swap
     · change relay A B (lantern V X.width X.material 0 *densityW A i)=_; rw [← aperture]; rw [Pi.smul_apply, smul_mul_assoc, map_smul]
     refine ⟨he.unit,?_⟩ ; change Beacon.ActionTest Θ 0 (F ⇑(t • f)) _; rw [show F ⇑(t • f)=t • F f from funext fun i=>mul_smul_comm t (Ring.inverse ((A.density B) i)) (f i)]; exact Orientation.acting Θ 0 _ _ w.val he.sees t
include ht
lemma tones (F:(c:Side)→ Density c 6→ Density c 6) (X Y:Insertion (S.side R i) 6)(hx:F _ ⇑X=⇑Y)(h:∀ (m:ℕ)(x:Insertion (S.side R (m+1)) 6),F _ (A.block m x)=A.block m (F _ ⇑x)): F _ ⇑(relay A j X)= ⇑(relay A j Y):=by
      induction ht using Nat.decreasingInduction with|self=> unfold relay; rw [S.entrance]; exact hx|of_succ i h' ih=> rw [stepped A X h',stepped A Y h',h,ih]
include hf hW hA h
variable (x y:Label d)(hg:Attest A V Θ j x y)
local notation "T"=> cereal A V j d
-- Invariant raw.Graded.Stream.
lemma wingUnit: Attest A V Θ j (Ξ.unit d) (Ξ.unit d):=by
     let x:= Ξ.unit d
     let v: Averaging:= none
     have hh:= bequeath A Θ Ξ L hf v hA W hW
     have hv:= hf.stone (Sn N) 0; have hX: draft S R L N j v x=1:=by unfold draft visitor; rw [smul_zero]; exact hv
     unfold Fuel setS at hh; rw [hX,mul_one] at hh; unfold Attest; rw [show cereal A V j d x = AllAt A j (A.regulator.density) from ?_]; exact hh
     change relay A j (lung V d _ 0*densityW A i)= _; rw [lute,one_mul]
     let Vl(v):= Sn v
     clear hh hX hW
     induction ht using Nat.decreasingInduction with
     | self=> unfold relay; rw [S.entrance]; rfl
     | of_succ i he ih=> apply ContinuousMap.coe_injective; rw [stepped A _ he, route A _ (lt_of_lt_of_le he h),ih]
include hg
lemma adjacent(a:Axis): Attest A V Θ j (Ξ.adj d a x) (Ξ.adj d a y):=by
    have hx:Tally Θ 0 y (A.density j) (tentT A none (lung V d x) j 0):=by rw[readingO]; exact hg
    have hp:= CardsT.resolveY A hA h ht a none (lung V d x) (lung V d (Ξ.adj d a x)) (frameAdj V Ξ x a) y Θ L Ξ hf W hW hx; rw [readingO] at hp; exact hp
lemma venus(p₀:EuPin)(s:Signed)(he:p₀.Lifts s) : Attest A V Θ j (Ξ.pin d p₀ x) (Ξ.pin d p₀ y):=by
    let Z:=lung V d; let Y:=Z (Ξ.pin d p₀ x); let F(c:Side): Density c 6→Density c 6:=Action.pin (n:=c) p₀ s
    have hh : Action.pin p₀ s ⇑(lung V d x 0)= ⇑(Y 0) :=by
            have h:=framePin V Ξ x p₀ s he 0; rw [Signed.act_zero] at h; exact h
    have hv : F (Sn i) ⇑(Z x 0 *densityW A i)=⇑(Y 0*densityW A i):=by
         funext U; exact (map_mul (Lining.Temper.shipP (Sn i) s p₀) ..).trans (congr_arg₂ HMul.hMul (congr_fun hh U) (congr_fun ((arrives A i h).1 p₀ s he) U))
    have heq:= tones A ht F (Z x 0 *densityW A i) (Y 0*densityW A i) hv (fun m z=>by unfold F Run.block; rw [step_brute,step_brute]; exact pin_travel (stitch S R m) _ s p₀ he (S.admissible m) _ _ (ContinuousMap.continuous z))
    have h:= Canvas.hinge s Θ p₀ (_ :Density (Sn j) 6) he hW.living (Ξ.pin d p₀ y) (fun x:Label d=> (⇑(L (Sn j) 0 x):Density _ 6)) (show Tally Θ 0 y (A.density j) (cereal A V j d x) from hg) hW.reading (by rw[pier A hA hW.siteM]; exact (arrives A j hW.siteM).1 p₀ s he) (by have he:= hf.pin (Sn j) y 0 s p₀ he; rw [Signed.act_zero] at he; exact he)
    unfold Attest; rw[show (⇑(cereal A V j d (Ξ.pin d p₀ x)))= F (Sn j) ⇑(cereal A V j d x) from heq.symm]; exact h
lemma lyreP : Attest A V Θ j (Ξ.parity d x) (Ξ.parity d y):=by
    let Z:=lung V d; let Y:=Z (Ξ.parity d x); let F(c:Side): Density c 6→Density c 6:=Action.parity (n:=c)
    have hh : Action.parity ⇑(lung V d x 0)= ⇑(Y 0) :=by
            have h:=frameP V Ξ x 0; exact h
    have hv : F (Sn i) ⇑(Z x 0 *densityW A i)=⇑(Y 0*densityW A i):=by
         funext U; exact (map_mul (Grass.grade) ..).trans (congr_arg₂ HMul.hMul (congr_fun hh U) (congr_fun ((arrives A i h).2.2.2.2) U))
    have heq:= tones A ht F (Z x 0 *densityW A i) (Y 0*densityW A i) hv (fun m z=>by unfold F Run.block; rw [step_brute,step_brute]; exact (TorusPCAC.Finite.block_grade (stitch S R m) (S.admissible m) _ (ContinuousMap.continuous _) _ _).symm)
    have h:= Canvas.hingeP Θ (_ :Density (Sn j) 6) (Ξ.parity d y) (fun x:Label d=> (⇑(L (Sn j) 0 x):Density _ 6)) (show Tally Θ 0 y (A.density j) (cereal A V j d x) from hg) hW.reading (by rw[pier A hA hW.siteM]; exact (arrives A j hW.siteM).2.2.2.2) (by have he:= hf.parity (Sn j) y 0; exact he)
    unfold Attest; rw[show (⇑(cereal A V j d (Ξ.parity d x)))= F (Sn j) ⇑(cereal A V j d x) from heq.symm]; exact h
lemma topC : Attest A V Θ j (Ξ.charge d x) (Ξ.charge d y):=by
    let Z:=lung V d; let Y:=Z (Ξ.charge d x); let F(c:Side): Density c 6→Density c 6:=Action.charge (n:=c)
    have hh : Action.charge ⇑(lung V d x 0)= ⇑(Y 0) :=by
            have h:=frameC V Ξ x 0; exact h
    have hv : F (Sn i) ⇑(Z x 0 *densityW A i)=⇑(Y 0*densityW A i):=by
         funext U; exact (map_mul (Lining.Temper.eveN (Sn i)) ..).trans (congr_arg₂ HMul.hMul (congr_fun hh U) (congr_fun ((arrives A i h).2.2.2.1) U))
    have heq:= tones A ht F (Z x 0 *densityW A i) (Y 0*densityW A i) hv (fun m z=>by unfold F Run.block; rw [step_brute,step_brute]; exact charge_shift (stitch S R m) _ (S.admissible m) _ _ (ContinuousMap.continuous z))
    have h:= Canvas.swingC Θ (_ :Density (Sn j) 6) hW.living (Ξ.charge d y) (fun x:Label d=> (⇑(L (Sn j) 0 x):Density _ 6)) (show Tally Θ 0 y (A.density j) (cereal A V j d x) from hg) hW.reading (by rw[pier A hA hW.siteM]; exact (arrives A j hW.siteM).2.2.2.1) (by have he:= hf.charge (Sn j) y 0; exact he)
    unfold Attest; rw[show (⇑(cereal A V j d (Ξ.charge d x)))= F (Sn j) ⇑(cereal A V j d x) from heq.symm]; exact h
lemma flora(u:FlavorTorus) : Attest A V Θ j (Ξ.flavor d u x) (Ξ.flavor d u y):=by
    let Z:=lung V d; let Y:=Z (Ξ.flavor d u x); let F(c:Side): Density c 6→Density c 6:=Action.flavor (n:=c) u
    have hh : Action.flavor u ⇑(lung V d x 0)= ⇑(Y 0) :=by
            have h:=frameF V Ξ u x 0; exact h
    have hv : F (Sn i) ⇑(Z x 0 *densityW A i)=⇑(Y 0*densityW A i):=by
         funext U; exact (map_mul (Lining.Temper.stroll (Sn i) u) ..).trans (congr_arg₂ HMul.hMul (congr_fun hh U) (congr_fun ((arrives A i h).2.2.1 u) U))
    have heq:= tones A ht F (Z x 0 *densityW A i) (Y 0*densityW A i) hv (fun m z=>by unfold F Run.block; rw [step_brute,step_brute]; exact flavor_shift (stitch S R m) _ (S.admissible m) _ _ (ContinuousMap.continuous z) _)
    have h:= Canvas.arrows Θ u (_ :Density (Sn j) 6) (Ξ.flavor d u y) (fun x:Label d=> (⇑(L (Sn j) 0 x):Density _ 6)) (show Tally Θ 0 y (A.density j) (cereal A V j d x) from hg) hW.reading (by rw[pier A hA hW.siteM]; exact (arrives A j hW.siteM).2.2.1 u) (by have he:= hf.flavor (Sn j) y 0 u; exact he)
    unfold Attest; rw[show (⇑(cereal A V j d (Ξ.flavor d u x)))= F (Sn j) ⇑(cereal A V j d x) from heq.symm]; exact h
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.wingUnit
#print axioms YM.Intag.Sprig.adjacent
#print axioms YM.Intag.Sprig.venus
#print axioms YM.Intag.Sprig.topC
#print axioms YM.Intag.Sprig.flora
#print axioms YM.Intag.Sprig.lyreP
