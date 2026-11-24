import YM.Mako.Pan
import YM.Mako.Ferns
import YM.Mako.Kona
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{W:Axis×Axis→ K.W} {A: Axle K (fun a b=>W (a,b))}{I:ℕ→ℕ} (J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)(hd:8 ≤ d)
local notation "Ω" => Free.Symbol d
local notation "Wd" => K.level d
set_option quotPrecheck false
local notation "Λ"=> tapeJ K W A hd
open Ortho (Skew)
open Org
include J
lemma vacation(p:Ortho.Skew) : ∀ v:Free.Symbol d,Tendsto (fun i=> (X.frame (I i) d).symm (tapeJ K W A hd p (X.frame (I i) d v))) atTop (𝓝 (rain p d v)):= goes J hd p
-- include trick binder!!
include H JQ B hd
lemma kinρ (a b:Axis): (Λ (Ortho.plane a b)).IsSemisimple:=by
    obtain ⟨p,h,h',-⟩:= outside a b b; exact semi _ _ (pinnacle H JQ W J.n A B hd a b p h h' 1 zero_lt_one)
lemma thawρ(a b:Axis):(rain (Ortho.plane a b) d).IsSemisimple:= convoy_sem (fun i=> X.frame (I i) d) _ _ (vacation J hd _) (kinρ J H JQ B hd a b)
noncomputable def flap: Skew →+ Module.End ℂ (Free.Symbol d):=
   { toFun u:=rain u d,map_add':= fun u v=> e_add J H JQ.h hd _ _
     map_zero':=by rw[← zero_smul ℝ (0:Skew),e_scal J H JQ.h hd]; simp }
noncomputable def flair : Skew →+ Module.End ℂ (Free.Symbol d →ₗ[ℂ] ↥(K.level d)):=
   { toFun u:= power (flap J H JQ hd u) (Λ u)
     map_zero':=by rw[map_zero,show Λ 0=0 from (yarn J H JQ hd).map_zero]; refine LinearMap.ext fun x=>LinearMap.ext fun i=>?_ ; rw[power_app]; simp
     map_add':= fun u v=>by rw [map_add,cash J H JQ hd,power_add] }
include R
lemma appoint:∃ m:Module.End ℂ (Ω →ₗ[ℂ] ↥(K.level d)), Split m (range fun i=> power (rain i d) (Λ i)):=by
     let Y:=flair J H JQ hd; let L:=fun i=> rain i d; apply surges Y
     · intro u v; change clip (power (rain u d) _) (power (rain v d) _)= _; rw[power_bracket,bridge J H JQ B hd R u v,show clip (rain u d) (rain v d)=_ from rue J H JQ.h hd u v R]; rfl
     · intro r p; change power (rain (r • p) d) (tapeJ K W A hd (r • p))=_; rw [e_scal J H JQ.h hd,gain J H JQ hd,power_smul]; rfl
     exact fun i j=> step _ _ (thawρ J H JQ B hd i j) (kinρ J H JQ B hd i j)
omit H R JQ B
variable {σ:ℂ→+*ℂ}[RingHomInvPair σ σ]
-- Prose applied on raw; correction exact even for improper/time, semilinear allowed
lemma approvals (m:Module.End ℂ (Free.Symbol d→ₗ[ℂ] ↥(K.level d)))(h: Split m (range fun i=> power (rain i d) (tapeJ K W A hd i))) (f:Label d ≃ₛₗ[σ] Label d)(g:K.W≃ₛₗ[σ] K.W) (hσ:Continuous σ) (hB:∀ i v, g (X.frame i d (projection v)).val=(X.frame i d (projection (f v))).val) (t:Skew→Skew)(ht:Surjective t)(hx:∀ i v,g (A.jet i v)= A.jet (t i) (g v)) (i:ℕ)(v:Label d):g (m (X.frame (I i) d).toLinearMap (projection v)).val= (m (X.frame (I i) d).toLinearMap (projection (f v))).val:=by
      obtain ⟨G,hG⟩:= kernelS (K.level d) g (by
              let X':=X.frame 0 d; have h(x:K.W) : x∈ K.level d↔ ∃ v:Label d,(X' (projection v)).val=x:=by
                     constructor
                     · intro hx; obtain ⟨w,hw⟩:=X'.surjective ⟨x,hx⟩; obtain ⟨v,rfl⟩:= Free.onto w; exact ⟨v,congr_arg Subtype.val hw⟩
                     rintro ⟨v,rfl⟩; exact (X' _).property
              refine le_antisymm ?_ ?_
              · rintro x ⟨v,hx,rfl⟩; obtain ⟨w,rfl⟩:=(h v).1 hx; exact (h _).2 ⟨f w,(hB 0 w).symm⟩
              intro v hv; obtain ⟨w,rfl⟩:=(h v).1 hv; obtain ⟨z,rfl⟩:= f.surjective w; exact Submodule.mem_map.mpr ⟨(X' (projection z)).val,(X' _).property,hB 0 z⟩)
      let F(k:ℕ):= X.frame (I k) d; rw[← hG]; apply congr_arg Subtype.val; refine lucent f F (@projection d) G (fun i=>rain i d) (tapeJ K W A hd) (vacation J hd) hσ Free.onto ?_ t ht ?_ m h i v
      · intro i j; apply Subtype.ext; rw[hG]; exact hB _ j
      intro i v; apply Subtype.ext; rw[hG]; change g (A.jet i _)= A.jet (t i) (G v).val; rw[hG]; exact hx i v.val
end YM.Mako
#print axioms YM.Mako.approvals
#print axioms YM.Mako.appoint
