import YM.Kauri.Apex
import YM.Siro.Dalia
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ Massive.Siro
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
set_option quotPrecheck false
local notation "X0"=> equip T ρ A.jet
include JQ H
lemma flapK(x:K.W)(a b:Axis): K.arc a (K.arc b x)=K.arc b (K.arc a x):=by
     refine detected H _ _ fun n p y hy=>?_ ; let k(w:K.W)(z:Points (n+1)):= K.total (n+1) z (Fin.cons w p); let D'(a:Axis):= Points.direction (0:Fin (n+1)) a; have h(v:K.W)(a:Axis)(z:Points (n+1))(hv:z∈conf _): D (D' a) (k v) z=k (K.arc a v) z:=by unfold k D'; rw[JQ.h.derivatives _ _ hv,Fin.cons_zero, Fin.update_cons_zero]; -- ok
     rw[heads,heads]; change k _ y=k _ y; rw [←h _ a _ hy, ← h _ b _ hy]; have hh(i:Axis): k (K.arc i x) =ᶠ[𝓝 y] D (D' i) (k x):= ((conf_open _).eventually_mem hy).mono fun z hz=> (h x i z hz).symm; rw[GermD (D' a) (hh b), GermD (D' b) (hh a)]; exact Analysis.commuteD (((JQ.h.smooth _ _).contDiffAt ((conf_open _).mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)) _ _
include J S B R
lemma belly : Siro.Brawl (F:=equip T ρ A.jet) K.total:=by
     have hb:= S.acts JQ.h (loans J H JQ B R)
     constructor
     · refine ⟨H.translation, fun l r h=> H.starry _ h _, H.parity, fun l v x y h p q ht hv=>?_, H.empty,H.functor,JQ.h.smooth,JQ.h.thick, fun n t a x hx b=> JQ.h.derivatives n x hx t a b,H.priests⟩
       refine H.flips l v x y p q h ?_ ?_; · cases p <;> exact ht
       cases q<;> exact hv
     · intro d; exact inferInstanceAs (FiniteDimensional ℂ (K.level d))
     · exact S.toll JQ.h (loans J H JQ B R)
     · intro g d h x hx; exact A.landed d h g _ hx
     · exact fun a b x=> flapK H JQ x a b
     · exact fun g a x=> (valiant J H JQ B R S g a x).symm
     · intro n p g x a hp hx
       cases n with
       | zero=>exact Finset.sum_empty
       | succ n=>
          have h:= Gust.line JQ.h H W J.n A B x hx p a g hp; refine Eq.trans ?_ h; change Siro.angQ (F:=X0) _ _ _ _= _; unfold Siro.angQ; apply Finset.sum_congr rfl; intro i _; let L:= (K.total (n+1) x).toLinearMap p i; change _= L (swirl K W A B g (x i) (p i)); unfold swirl; rw[map_add,map_sum,← wins J H JQ B R S]; apply congr_arg₂ _ rfl; apply Finset.sum_congr rfl; intro j _; rw[map_smul]; rfl
     · exact T.even JQ.h
     · exact T.reflex JQ.h
     intro a; let s:= Signed.mirror a; exact ⟨T.spin (flipC a),fun n p x h=>by
          have ht:= (H.discrete n x h (flipC a) s (couture a) p).symm; rw [show (flipC a).coord=Signed.reflect a from couture a] at ht; exact ht⟩
lemma ascent(n:ℕ)(x:Points n)(hx:x∈ conf n)(p:Fin n→K.W)(s:EuPin): K.total n (Points.move s.coord x) (ρ s ∘ p)= K.total n x p:=by
     let Y(t:EuPin):Prop:=∀ (x:Points n)(h:x∈conf n)(p:Fin n→ K.W),K.total _ (Points.move t.coord x) (ρ t ∘ p)= K.total n x p; let U:Subgroup EuPin:= {
           carrier:={x|Y x},one_mem':=fun x hx p=>by rw[map_one,show EuPin.coord 1=1 from rfl, Siro.one_move]; rfl
           mul_mem':=by intro z w (hz:Y z) (hw:Y w) x hx p; rw[show (z*w).coord=z.coord*w.coord from rfl,Siro.mul_move,map_mul]; exact (hz _ (Points.move_in _ hx) (ρ w∘p)).trans (hw x hx p)
           inv_mem':=by
                  intro z (hz:Y z) x hx p; rw [show (z⁻¹).coord=z.coord⁻¹ from rfl]; have he:= hz _ (Points.move_in (z.coord⁻¹) hx) (ρ z⁻¹∘p); rw [Siro.unmove, show ρ z ∘ (ρ z⁻¹∘p)=p from ?_] at he; exact he.symm
                  funext i; rw [map_inv]; exact (ρ z).apply_symm_apply _ }
     have ht : s∈U:=by
           apply engenders; · intro p s hs; intro x hx v; rw [S.acts JQ.h (loans J H JQ B R) _ _ hs]; exact H.discrete _ x hx p s hs v
           intro g i x hx v; exact Siro.lines (belly J H JQ B R S) (fun d hd v hv p=> S.dizzy JQ.h (loans J H JQ B R) v hd hv p) (fun v p t h s=>S.smooths JQ.h (loans J H JQ B R) v p t h s) g (oathU g) (tour g) _ hx v i -- check instances
     exact (show Y s from ht) x hx p
lemma heat : Fields.Euclidean (F:=X0) K.total := Tarn.european T H JQ ρ A.jet (fun t n x hx u=> ascent J H JQ B R S n x hx u t)
end YM.Mako
#print axioms YM.Mako.ascent
#print axioms YM.Mako.heat
