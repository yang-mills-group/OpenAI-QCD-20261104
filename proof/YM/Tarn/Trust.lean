import YM.Tarn.Plush
import YM.Fir.Pear
import YM.Fir.Prism
/-! Quotient powers and concrete non-null domain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Zodiac Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag.Vale
open scoped Topology ContDiff BigOperators Classical
open Function Sash
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
variable {Z:SpaceZ}(H:Ability P φ Z)(h:Cresc Z){M:∀ d:ℕ,Axis→Label d→ₗ[ℂ] Label (d+2)} (he:Gains M Z)
variable (s: Sash G φ) (hz:DriftF G φ)
include H hp hφ hr s hz
lemma builds : Cresc Z:=by
    apply monotone_nat_of_le_succ; intro n; obtain ⟨F,h⟩:= increment hp hr hφ s H hz n; rintro v ⟨p,rfl⟩; exact ⟨F p,funext (fun x=> (h x.n x.t x.x x.hx x.p p).symm)⟩
omit hz hr
lemma caulk (d:ℕ): Injective ((plume Z d).comp (s.R d).toLinearMap):=by
     let F:=(plume Z d).comp (s.R d).toLinearMap
     apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr; intro v hv
     apply s.known hp hφ H d; intro k; let V:= s.L d k; let S:Story:= ⟨2,sea G d,fun _=> ⟨d,V⟩,1,stage G d⟩; have h':(zodiac Z d (s.R d v)) S=0:= congr_fun (congr_arg (fun x:foliage Z=> x.val) hv) S
     have hq(u:Label d): handle Z (fun i:Fin 2=> ⟨d,(![V,u] i)⟩) S.x = puts Z S.x S.t S.p d u:=by
         apply feel_eq; intro i; fin_cases i <;> rfl -- maybe classical update
     exact (hq _).trans h'
include hr
lemma rafters (d:ℕ):LinearMap.range ((plume Z d).comp (s.R d).toLinearMap) = LinearMap.range (plume Z d):=by
    refine le_antisymm ?_ ?_; · rintro _ ⟨u,rfl⟩; exact LinearMap.mem_range_self ..
    rintro _ ⟨z,rfl⟩; refine ⟨s.A none d z,?_⟩; apply Subtype.ext; funext i; exact (grasp hp hr hφ s H d i.t i.p z i.x i.hx).symm
omit H hr hp hφ s
include he
lemma motions {d f:ℕ}(u:Label d)(v:Label f)(hx: plume Z d u=plume Z f v)(a:Axis): plume Z _ (M d a u)=plume Z _ (M f a v):=by
     apply Subtype.ext; funext i; change puts Z i.x i.t i.p _ (M d a u)= puts Z i.x i.t i.p _ (M f a v); rw [← he.partsH d a u _ i.hx, ← he.partsH f a v _ i.hx] -- notation may fail
     apply GermD; filter_upwards [(conf_open i.n).mem_nhds i.hx] with x h; exact congr_fun (congr_arg (fun v:foliage Z=> v.val) hx) ({i with x:=x,hx:=h}:Story)
include h
lemma partials : ∃ Φ: Axis→ foliage Z →ₗ[ℂ] foliage Z, ∀ d a (p:Label d), Φ a (plume Z d p)= plume Z _ (M d a p):=by
    let T':= firstV Z h; let Φ(a:Axis)(p:foliage Z):=plume Z _ (M (T' p).1 a (T' p).2); have hp (d:ℕ)(a:Axis)(p:Label d): Φ a (plume Z d p)=plume Z _ (M d a p):= motions he (T' (plume Z d p)).2 p (show signets Z (T' (plume Z d p))=plume Z d p from (h.bell (plume Z d p)).choose_spec) a
    let F(a:Axis): foliage Z→ₗ[ℂ] foliage Z:= {
         toFun:=Φ a
         map_add':=fun x y=>by
             obtain ⟨d,p,q,rfl,rfl⟩:= h.allure x y; rw[←map_add,hp,hp,hp,map_add,map_add]
         map_smul':=fun κ x=>by
             obtain ⟨d,p,hp'⟩:= h.sealed x; rw [←hp',←map_smul,hp,hp,map_smul,map_smul]; rfl }
    exact ⟨F,hp⟩
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.caulk
#print axioms YM.Massive.Tarn.partials
