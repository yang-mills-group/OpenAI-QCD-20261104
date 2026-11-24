import YM.Iceberg.Fleck
import YM.Vern.Plush
import YM.Lobo.Nectar
set_option maxHeartbeats 640000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {φ:ℕ→ℕ}
variable (hf:Foil P K T)(HQ:K.Harmony P φ)
noncomputable def turf(a:Axis)(r:ℝ)(u v:K.W):ℂ:= K.total 2 (points (![0,r • basis a])) (![T.adj a u,v])
variable (a:Axis)(r:ℝ)(hr:0<r)
include hr HQ hf
lemma cofin (p:K.W) (h:p≠0): 0<(turf (T:=T) a r p p).re:=by
      obtain ⟨X⟩:= Kernel.host (shines HQ.h hf a); let H:=turf (T:=T) a r p p; have hz:H≠0:=credible HQ.h hf a p hr h; let r' := r/2; let Y:=X.plant (postX a p r' (half_pos hr)); have hy:inner ℂ Y Y=H:= (signal hf a r' r' p X (half_pos hr) (half_pos hr)).trans (congr_arg (fun b=>iconP (T:=T) a b p) (add_halves r)); change 0< H.re; rw [←hy]; apply (re_inner_self_pos (𝕜:=ℂ)).mpr; intro h; apply hz; rw [←hy,h]; simp
lemma top_co(y z:K.W): star (turf (T:=T) a r y z)= turf a r (T:=T) z y:=by
      obtain ⟨X⟩:= Kernel.host (shines HQ.h hf a); let p:=r/2; let F(z:K.W):= X.plant (postX a z p (half_pos hr))
      have hs(y z:K.W):inner ℂ (F y) (F z)= turf a r (T:=T) y z:=by
              rw [show inner ℂ (F y) (F z)= _ from (X.measure ..)]; unfold oppositeS; change tone [(Ortho.move (Signed.reflect a) (pet a p),T.adj a y),(pet a p,z)]=_; rw [reflectedM]; let Z := points (![pet a (-p),pet a p]); have hz:Z∈conf 2:=by
                       have h:pet a (-p)≠pet a p:=by intro h; have hh: -p=p:=by simpa [pet,basis] using congr_arg (fun b:E4=> b a) h
                                                     linarith [show 0<p from half_pos hr]
                       intro i j he; fin_cases i<;>fin_cases j<;> first | rfl| exact (h he).elim| exact (h he.symm).elim
              unfold tone; calc
                _=K.total 2 Z (![T.adj a y,z]):=by
                     congr 1; · apply congr_arg (K.total 2); apply PiLp.ext; intro i; fin_cases i<;>rfl
                     ext1 i; fin_cases i<;>rfl
                _= _:=by
                         rw [← hf.translation 2 Z hz (pet a p)]; refine congr_arg (fun x:Points 2=> K.total _ x _) ?_; ext1 i; fin_cases i; · change pet a (-p)+pet a p=0; simp
                         change pet a p+pet a p=r • basis a; unfold pet; rw [←add_smul, add_halves]
      rw [←hs,←hs]; exact inner_conj_symm _ _ -- order
noncomputable def entryQ (d:ℕ): Tide ↥(K.level d):=by
       let H:= points (![0,r • basis a]); let G:= (K.total 2 H); let K'(x: K.W):= G.toLinearMap (![T.adj a x, 0]) 1; have h(x y:K.W):K' x y= turf a r (T:=T) x y:=by
              apply congr_arg G; funext i; fin_cases i<;>simp
       exact {knot:=fun i j=>turf a r (T:=T) i.val j.val, positive:=fun x hx=>cofin hf HQ _ _ hr x.val (by intro h; exact hx (Subtype.ext h)), con:=fun i j=> top_co hf HQ _ _ hr i.val j.val, add:=fun i j k=>by rw[←h,←h,←h]; exact map_add (K' i.val) j.val k.val, sep:=fun c x y=>by rw [←h,←h]; exact map_smul ..}
end YM.Vern
#print axioms YM.Vern.entryQ
