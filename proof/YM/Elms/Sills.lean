import YM.Elms.Mir
/-! # Equation observables: orbit, reflection disjoint at the depth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
local notation "τ"=> su.probHaar
local notation "s"=>Signed.mirror a
local notation "V"=> Lat.Fields n 6
local notation "Fω"=> Insertion n 6
local notation "E"=>Patria.Exposure.eyeP n a
lemma labelled_arm (p:Site n)(g:Frame n): E *Lat.rotates 6 g=Lat.rotates 6 (g∘axisT a)* E:=by
      unfold eyeP; rw [Ferry.roller,Ferry.sight,Ferry.sight,spar_spar,spar_spar]; apply congr_arg; funext i; rw [Matrix.smul_mul,Matrix.mul_smul]; exact congr_arg (fun z:Bundle=> _ • z) (interlace ..).symm.eq -- first arg equal by def
lemma shapes (x:Fω)(g:Frame n): transform g (unia a x) = unia a (transform (g ∘ axisT a) x):=by
     ext1 U; change slots 6 g (unia a x (Lattice.gauge g U))=_; rw [heroY,heroY,face_rot];
     have ht: affine (s) (0:Site n)=axisT a:=funext fun i=>by simp [affine,axisT];
     rw [ht]; exact (tilt_through _ _ _ _ (eye_star ..) (eye_star ..) (labelled_arm a 0 g).symm.symm _).symm -- e: E*V? V=g actual, yes
lemma routed (x:Fω)(h:Lat.Invariant x): Lat.Invariant (unia a x):=fun g=> by rw [shapes,h]
-- sentry untouched outside set. Extend by preimages. Finite map.Motions by selecting a linear left lift of range.
lemma passed (S T:Set (Site n))(h:Set.MapsTo (axisT a) S T)(x:Dirac (Deck S 6)): tilt E (pass (setDay S) x) ∈ LinearMap.range (pass (setDay T (F:=6))).toLinearMap:=by
    let J:=pass (setDay T (F:=6)); let L:=pass (setDay S (F:=6)); let Q:=L.toLinearMap; let W:= J.toLinearMap; let B:=LinearMap.range W; let E0 : Dirac (Modes n 6) →ₛₗ[starRingEnd ℂ]Lat.Fields n 6:= tilt E
    suffices hv :∀ x:Dirac _, E0 (L x)∈ B from hv x
    intro x
    have hg {y z:Lat.Fields n 6}(hf:y∈B)(hh:z∈B): y*z∈B:=by obtain ⟨y,rfl⟩:=hf; obtain ⟨z,rfl⟩:=hh; exact ⟨y*z,map_mul J ..⟩
    have hu: (1:Lat.Fields n 6)∈B:=⟨1,map_one J⟩; have hf(i:Pairs (Deck S 6)): E0 (L (Grass.atom i))∈B:=by
        have he (y:↥S)(w:Dike)(q: Bool): E0 (L (lineT q (RP.place y w)))∈ B:=by
            rw [show L _=lineT q (RP.place y.val w) from ?_,show E0 _= _ from hemis (n:=n) a q w y.val]; rotate_left
            · cases q; exact pass_psi ..; exact pass_bar ..
            refine B.smul_mem _ (B.sum_mem fun i _=> B.smul_mem _ ?_); let z :↥T:=⟨axisT a y.val,h y.2⟩; refine ⟨lineT (!q) (RP.place z i),?_⟩; cases q; exact pass_bar ..; exact pass_psi ..
        rcases i with ⟨⟨y,w⟩,f⟩|⟨⟨y,w⟩,f⟩; exact he y (w,f) false; exact he y (w,f) true -- binder
    have hv(l:List (Pairs (Deck S 6))): E0 (L (l.map Grass.atom).prod)∈B:=by
        induction l with
        | nil=> rw [List.map_nil,List.prod_nil,map_one,show E0 1= _ from tilt_one _]; exact hu
        | cons i l ih=> rw [List.map_cons,List.prod_cons,map_mul]; exact (tilt_mul E _ _).symm ▸ hg ih (hf i) -- symm ▸ ?
    rw [← Grass.write x,map_sum,map_sum]; apply Submodule.sum_mem; intro i _; obtain ⟨y,-,-,he⟩:=Grass.expression i; rw [map_smul,map_smulₛₗ,he]; apply Submodule.smul_mem; simpa only [List.map_ofFn] using hv (List.ofFn y)
lemma flooring {X:Insertion n 6}(S:Set (Site n))(h: LocalOn S X) (H:∀ U,X U∈ LinearMap.range (pass (setDay S (F:=6))).toLinearMap) : Floors S X:=by
    let M:Dirac (Deck S 6) →ₗ[ℂ] Lat.Fields n 6:= (Grass.pass (setDay S (F:=6))).toLinearMap; let W := LinearMap.range M; let f (U:Grid n):W:=⟨X U,H U⟩; have hf: Continuous f:= X.continuous.subtype_mk _
    obtain ⟨A,hA⟩:= M.rangeRestrict.exists_rightInverse_of_surjective M.range_rangeRestrict
    refine ⟨fun x=>A (f x),A.continuous_of_finiteDimensional.comp hf,fun x y hp=> congr_arg A (show f x=f y from Subtype.ext (h x y hp)),fun U=>?_⟩
    exact congr_arg Subtype.val (LinearMap.congr_fun hA (f U)).symm
lemma sectorsT(x:Fω){S T:Set (Site n)}(hx: Floors S x)(h: Set.MapsTo (axisT a) S T) : Floors T (unia a x):=by
    obtain ⟨f,hf,hF,hY⟩:=hx; refine flooring T ?_ ?_
    · intro U u he; rw [heroY,heroY,hY,hY,hF _ _ (RP.sees s 0 U u (show Set.MapsTo (affine s 0) _ _ from fun a hg=> by simp only [affine,add_zero]; exact h hg) he)]
    intro U; rw [heroY,hY]; exact passed a S T h _
lemma turn_cap {k:ℕ} : Set.MapsTo (axisT a) (Outer k (wrap n o)) (Outer k (wrap n (axisT a o))) :=by
   intro x hx; change k < separation _ _; unfold axisT; rw [←wrap_signed,separation_signed]; exact hx
lemma avg_eye (x:Insertion n 6)(hv:P.t=0): P.average (unia a x)=star (P.average x):=by
   suffices h:P.raw (unia a x)=star (P.raw x) by
      have he: star (P.Z) = P.Z:= (congr_arg star P.Z_real).trans ((Complex.conj_ofReal _).trans P.Z_real.symm)
      simp only [Regulator.average,h,LinearMap.smul_apply,smul_eq_mul,star_mul,star_inv₀,he]; rw [mul_comm]
   
   let A(U:Grid n): ℂ:= star (ber _ (P.density U*x U)); have hA :Continuous A:= (continuous_ber.comp (P.density.continuous.mul x.continuous)).star
   have he(U:Grid n): ber _ (P.density U * unia a x U) = A (pull s 0 U):=by
       let f:=P.density; let p:=pull s (0:Site n) U; have hT: Grass.Plus (f U):=by change Grass.grade (_)=_; unfold f; simp_rw [Regulator.density_apply,map_smul, show Grass.grade (gauss (P.D U))=_ from gauss_plus _];
       rw [show f U*unia a x U= unia a x U*f U from (hT.central _).eq.symm, heroY, show f U=tilt E (f p) from ?_, ← tilt_mul, tilt_amp _ (eye_sq _ ) _];  exact (congr_fun (eye_pivot a P hv) U).symm.trans (eye_value ..)
   change (∫ U:Grid n, ber _ (P.density U*unia a x U) ∂prior su n)=star (∫ U:Grid n,ber _ (P.density U*x U)∂prior su n); simp_rw [he]; rw [Complex.star_def,← integral_conj]; let M:=prior su n; change (∫ U,A (pull (Signed.mirror a) (0:Site n) U) ∂M)=∫ U,A U ∂M; have hv: MeasurePreserving (pull (K:=su.El) s (0:Site n)) M M:=prior_pull ..; nth_rw 2 [← hv.map_eq]; rw [integral_map hv.aemeasurable hA.aestronglyMeasurable]
-- grade and null anywhere in word order.
def moon (q:Bool)(x:Fω): Prop:= ∀ U, Grass.Hom q (x U)
def permuteD (x:Insertion n 6):Fω:=⟨fun U=>Grass.grade (x U),grade.toLinearMap.continuous_of_finiteDimensional.comp x.continuous⟩
lemma gradedF {x:Fω}{S:Set (Site n)} (h:Floors S x): Floors S (permuteD x):=by
    obtain ⟨f,hf,hF,hx⟩:=h; refine flooring S ?_ ?_; swap
    · intro U; change Grass.grade (x U)∈ _; rw [hx]; exact ⟨Grass.grade (f U),(embed_grade (A:=Pairs (Deck S 6)) (B:=Pairs (Modes n 6)) (Sum.map (setDay S) (setDay S)) _).symm⟩
    intro U X h; change Grass.grade (x U)=Grass.grade (x X); rw [hx,hx,hF _ _ h]
lemma moon_mir {x:Fω}{p:Bool}(h:moon p x):moon p (unia a x):=by
     intro U; specialize h (pull s (0:Site n) U); cases p
     · change grade (unia a x U)=_; rw [heroY,tilt_grade, show grade _=_ from h]; -- scope
     change grade _= - _; rw [heroY,tilt_grade, show Grass.grade (x _)=_ from h,map_neg] -- infer
lemma balance {x:Fω}{p:Bool}(h:moon p x)(y:Fω) : y*x=x*(if p then permuteD y else y):=by ext1 U; change y U*x U=x U*_ ; cases p; exact Plus.central (show Grass.Plus (x U) from h U) _; exact (show Grass.Minus (x U) from h U).slides _
lemma sunny (h:P.t=0){x:Fω}{k:ℕ}{p:Bool}(hf:moon p x)(he: NullOn P x (Outer k (wrap n o))): NullOn P (unia a x) (Outer k (wrap n (axisT a o))):=by
    intro y hy; rw [← (show unia a (unia a y*x)=unia a x*y from by rw [unia_prod,againZ]),avg_eye P _ _ h,balance hf,he _,star_zero]
    have ht:= sectorsT a y hy (show Set.MapsTo (axisT a) _ _ from (by have h:= turn_cap (n:=n) (k:=k) (axisT a o) a; rwa [axis_sq] at h)); split; exact gradedF ht; exact ht
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.routed
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.sunny
