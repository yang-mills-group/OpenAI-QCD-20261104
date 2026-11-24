import YM.Sunda.Beam
import YM.Sunda.Genre
import YM.Mako.Ears
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
open Sunda Lobo
variable (k:Tri)(t:ℝ)
lemma tre_map {U Y:Type} [AddCommGroup U][Module ℂ U][AddCommGroup Y][Module ℂ Y] {f:ℝ→U}(hf:f∈Tres U)(F:U→ₗ[ℂ]Y): (fun t=> F (f t))∈Tres Y:=by
      obtain ⟨v,h,A,B,k⟩:=hf; exact ⟨_,uni_map h F,F A,F B,fun t=>by dsimp only; rw [k,map_add,map_add,map_smul,map_smul]⟩
local notation "Q" t:arg=> (pathW k t)
local notation "q"=> (Real.pi/2)
local notation "hπ"=>Real.pi
lemma headed : ∃ s:Signed,(Q hπ).Lifts s:=by
     refine ⟨Cup k * Cup k,?_⟩; have he:= fL k; have hh : pathW k hπ = SpinQ k*SpinQ k:=by rw [show SpinQ k*SpinQ k=pathW k (q+q) from (SpinParity.additive (treks k) ..).symm]; congr 1; ring
     rw [hh]; change euca (SpinQ k*SpinQ k)=Signed.inclusionO (Cup k*Cup k); rw [map_mul,map_mul,show euca (SpinQ k)=_ from he]; rfl
include R B H J JQ S
lemma bulky (w:K.W)(hx:w∈K.level 8): (fun t=>ρ (Q t) w)∈Tres K.W:=by
      obtain ⟨F,hF⟩:=loans J H JQ B R _ (le_refl 8); obtain ⟨v,hv⟩:= F.surjective ⟨_,hx⟩; obtain ⟨p,rfl⟩:=Free.onto v; rw [← show (F (projection p)).val=w from congr_arg Subtype.val hv]
      simp_rw [S.tones _ _ F hF, clanP]; exact tre_map (breaths k P.sym p) ((K.level 8).subtype ∘ₗ F.toLinearMap ∘ₗ projection) -- arg name U
lemma lows (w:K.W)(hx:w∈K.level 8)(hh:w-ρ (Q q) w+ρ (Q hπ) w-ρ (Q (hπ+q)) w=0): (fun t=>ρ (Q t) w)∈Uno K.W:=by
      refine gleams (bulky J H JQ B R S k w hx) (fun t=>?_); have he:=congr_arg (ρ (Q t)) hh; rw[map_sub,map_add,map_sub,map_zero] at he; rw [add_assoc, SpinParity.additive (treks k),SpinParity.additive (treks k),SpinParity.additive (treks k),map_mul,map_mul,map_mul]; -- rewrite may refer wrong add
      convert he using 1; simp [SpinParity.additive (treks k)] -- ..
variable {d:ℕ} (ht:d<8)(F:Free.Symbol d≃ₗ[ℂ] ↥(K.level d))(hF:Prose F T)
include hF ht
lemma kisses (x: Label d)(p: EuPin): ρ p (F (projection x)).val=(F (projection (P.sym.pin d p x))).val:=by
     let Y(p:EuPin):Prop:=∀ v:Free.Symbol d, ρ p (F v).val= (F (caravan R d p v)).val; let U:Subgroup EuPin:={
            carrier:={p|Y p},one_mem':=fun v=>by simp
            mul_mem':=by intro p s (hp:Y p)(hs:Y s) v; rw[map_mul,map_mul,LinearEquiv.mul_apply,hs,hp]; rfl
            inv_mem':=by
                 intro p (hp:Y p) v; apply (ρ p).injective; rw [hp,← LinearEquiv.mul_apply (ρ p), ← map_mul]; simp }
     have hv(p:EuPin)(s:Signed)(h:p.Lifts s): p∈ U:=by
            intro v; obtain ⟨t,rfl⟩:= Free.onto v; rw [S.acts JQ.h (loans J H JQ B R) _ _ h, clanP, hF.rotates t p s h]
     let i:Tri:= 0; let f:=pathW i
     have h': p∈U:=by
            apply genreK i U hv _ p; intro t v; obtain ⟨x,rfl⟩:= Free.onto v; let X:=projection x; let z:= (F X).val; let w(t:ℝ):=ρ (f t) z; let y(t:ℝ):=(F (caravan R d (f t) X)).val
            have hy : y∈ Uno K.W:=by
                   unfold y X; simp_rw [clanP]; exact uni_map (living i P.sym ht x) ((K.level d).subtype ∘ₗ F.toLinearMap ∘ₗ projection) -- infer
            have he:w 0=y 0:=by unfold w y f; rw [(treks i).1,map_one,map_one]; rfl
            have hz:w q=y q:= (show Y (f q) from hv (f q) (Cup i) (fL i)) _; obtain ⟨s,hs⟩:=headed i; have hh:w hπ=y hπ:=(show Y (f hπ) from hv _ s hs) _
            have ht': w (hπ+q)=y (hπ+q):=by
                   have ht:f (hπ+q)=f hπ*f q:= SpinParity.additive (treks i) _ _
                   exact (show Y (f (hπ+q)) from (show f (hπ+q)∈ U from ht ▸ U.mul_mem (hv _ s hs) (hv _ (Cup i) (fL i)))) _
            have hw:w∈Uno K.W:= lows J H JQ B R S i z (JQ.h.slope ht.le (F X).property) (by
                 have hv:z=w 0:=by unfold w f; rw[(treks i).1,map_one]; rfl
                 change z-w q+w hπ-w (hπ+q)=0; rw[hv,he,hz,hh,ht']; simpa only [zero_add] using echoes hy (0:ℝ))
            exact congr_fun (Sunda.known hw y hy he hz hh) t
     have hw:=(show Y p from h') (projection x); rw [clanP] at hw; exact hw
omit hF ht
lemma tides (x:K.W)(hx:x∈K.level d)(p:EuPin): ρ p x ∈ K.level d:=by
      by_cases h:d<8
      · let F:=X.frame 0 d; obtain ⟨v,hv⟩:= F.surjective ⟨x,hx⟩; obtain ⟨w,rfl⟩:=Free.onto v; rw [← show (F (projection w)).val=x from congr_arg Subtype.val hv, kisses J H JQ B R S h F (X.leaders 0 d) w]; exact Subtype.property _
      exact S.dizzy JQ.h (loans J H JQ B R) x (le_of_not_gt h) hx p
lemma loft : (X0).System (res C P φ):=turners T H JQ ρ A.jet (S.acts JQ.h (loans J H JQ B R)) (S.fling JQ.h (loans J H JQ B R)) (fun d=> tides J H JQ B R S) (fun p u x=> (S.plum JQ.h (loans J H JQ B R) p x u).symm) (fun X u f h=>by
      have he:= S.smooths JQ.h (loans J H JQ B R) u X f h 0; rw [h.1,map_one] at he; exact he)
end YM.Mako
#print axioms YM.Mako.loft
#print axioms YM.Mako.kisses
#print axioms YM.Mako.lows
