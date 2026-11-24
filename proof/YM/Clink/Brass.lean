import YM.Clink.Reams
import YM.Clink.Trench
/-!
  Whole injection equalities at any stop. Moment link scenarios. Linear mix across exact unique Tally.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays TableT
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
open Next.Free QCD.Entr QCD.Entr.Meridian QCD.Flume
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
local notation "c'"=> S.side R k
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(u:Averaging)(T:TaperHol)(W:QCD.Flume.Plan d)(H:Train d)(z:ℝ)
local notation "G"=> corm (i:=i) A d W H z a
local notation "Y"=> marque (i:=i) A true a
local notation "φ"=> A.density k
local notation "Q" X:arg=> foil φ (report A X u k 0)
local notation "E" X:arg=> Gall.viaP A X u
variable (F: Cover→Insertion (S.side R i) 6)
include hi
-- fees for equality of stencil-U columns relative ACT with tilde variant z, Z
omit hi
lemma capsT (P: Site M →Insertion M 6)(hp:F=P∘wrap M): Gall.viaP A F u i=∑ j, P j:=by
       unfold Gall.viaP; simp_rw[arrivesHere,hp]; simp [Function.comp_def] -- Finset err
lemma paidT (P:Site M→Insertion M 6)(hp:F=P∘wrap M)(hk:k ≤ i)(x:Sail)(hx:u=Option.some x): Gall.viaP A F u k= ((ratioTo S i k :ℝ)^4)⁻¹ • S.toStop R A.β A.w i k (Gall.viaP A F u i):=by
       rw [capsT A u F P hp,hp]; exact scales A P x hk u hx
lemma wool (hk:k ≤ i) (x:Sail)(hx:u=Option.some x): Gall.viaP A (G s) u k= Gall.viaP A (Y s) u k :=by
        let X':=(G s); have hm:X'=(fun b'=>X' (lift b'))∘wrap M:=by
              ext1 u; apply ContinuousMap.ext; intro j; let z:=wrap M u; let v:=actor A i; change Wagon _ z j (v j)+ (v j)*_ = Wagon _ (wrap M (lift z)) j (v j)+(v j)*(forkT _ (wrap M (lift z)) _ _ _).val; rw [wrap_lift]
        rw [paidT A u X' _ hm hk x hx, Oren.port, paidT A u (Y s) (fun i=>Y s (lift i)) (_: Y s=(fun i=>Y s (lift i))∘ wrap M) hk x hx]
        ext1 b; apply ContinuousMap.ext; intro i; change Wagon _ _ _ _= Wagon _ _ _ _; rw [wrap_lift]
lemma ZW(hk:k≤ i)(x:Sail)(hx:u=Option.some x) : Gall.viaP A (sprigs (i:=i) A a s) u k=0:=by
       let F:=sprigs (i:=i) A a s; have he:F=(fun b'=>F (lift b'))∘ wrap M:=by
            ext1 i; apply ContinuousMap.ext; intro U; change (_)*(sprig a _ _ _).val= _*(sprig a _ _ _).val; rw [wrap_lift]
       rw[paidT A u F _ he hk x hx,sailsZ A]; erw[map_zero]; rw[smul_zero]
-- rune: rot from chart and T at EVERY.K.Shelf. transfer Q after receipt. singular ments still ok near identity.
include hA hi
variable (i' j':Fiber)(x:Sail)(hx:u=Option.some x) (hk:k ≤ i)(hV:∀ᶠ U' in 𝓝 1, IsUnit ((A.density k) U'))
local notation "r1"=>river1 t b i' j'
local notation "r2"=>river2 s t b i' j' g
include hx hk hV
lemma ζblink (F D:Cover→Insertion (S.side R i) 6)(hZ:Gall.viaP A F u k=Gall.viaP A D u k)(hX: Chart n (Q F) 1)(hY:Chart n (Q D) 1)(he:TideT A u i (report A F u))(hh:TideT A u i (report A D u))(hn:1 ≤ n): r1 (Q F)=r1 (Q D)∧ r2 (Q F)=r2 (Q D):=by
       obtain ⟨hf,hf'⟩:=rune A hk F u he hA (hk.trans hi) b i' j' s t g hV hX hn; rw [hZ] at hf hf'; obtain ⟨hd,hd'⟩:=rune A hk D u hh hA (hk.trans hi) b i' j' s t g hV hY hn; have ht: (Fintype.card (Site c'):ℂ)≠0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'; exact ⟨mul_left_cancel₀ ht (hf.symm.trans hd),mul_left_cancel₀ ht (hf'.symm.trans hd')⟩
lemma ξblink (F:Cover→Insertion (S.side R i) 6)(hZ:Gall.viaP A F u k=0)(hX:Chart n (Q F) 1)(he:TideT A u i (report A F u))(hn:1≤ n) : r1 (Q F)=0∧ r2 (Q F)=0:=by
       obtain ⟨hf,hh⟩:=rune A hk F u he hA (hk.trans hi) b i' j' s t g hV hX hn; have ht: (Fintype.card (Site c'):ℂ)≠0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'; rw [hZ,show foil φ ⇑(0: Insertion c' 6)= (0: Density c' 6) from (?_),zeroRiver1] at hf; rotate_left; · ext1 i; exact mul_zero _
       rw [hZ,show foil φ ⇑(0: Insertion c' 6)=(0:Density c' 6) from (?_),zeroRiver2] at hh; rotate_left; · ext1 i; exact mul_zero _
       exact ⟨(mul_eq_zero.mp hf.symm).resolve_left ht,(mul_eq_zero.mp hh.symm).resolve_left ht⟩
omit hV hi hA hx hk
-- Tally linear sum on experiment follows via Needle
variable (f z':Flavor 6→ℂ)
local notation "R*" X:arg=> report A X u k 0
variable (B:Cover→Insertion (S.side R i) 6)
lemma laysP : R* (F+B)=(R* F)+(R* B):=by
       unfold report visitor; rw [roles, training, Pi.add_apply, roles, roles]; exact map_add (relay A k) _ _ -- syntax maybe function roles needs b arg; compare Stray
lemma orchid (D: RawVec 10)(Yv:Flavor 6→ RawVec 10)(Z: Flavor 6→ RawVec 10)(U': RawVec 10)(hD:Tally T 0 (D.val s) φ (R* (G s)))(hY:∀ p,Tally T 0 ((Yv p).val s) φ (R* (marque (i:=i) A false p s)))(hZ:∀ p, Tally T 0 ((Z p).val s) φ (R* (sprigs (i:=i) A p s)))(h:Tally T 0 (U'.val s) φ (R* (lobbyR (i:=i) A d W H z a f z' s))) : U'.val s= (D+ ∑ i:Flavor 6,(f i • Yv i+ z' i • Z i)).val s:=by
       let V (a:Flavor 6):= bead (i:=i) A f z' a; let ZB(p:Flavor 6):= f p • Yv p + z' p • Z p; have hh(p:Flavor 6): Tally T 0 ((ZB p).val s) φ (R* (V p s)):=by
             unfold V ZB; rw [show bead A f z' _ s= f p • marque A false p s+z' p • sprigs (i:=i) A p s from rfl,laysP,trackScale,trackScale]; exact Needle.totalY _ _ _ _ _ _ _ (Needle.quotaY _ _ _ _ _ _ (hY p)) (Needle.quotaY _ _ _ _ _ _ (hZ p))
       suffices hv:∀ X:Finset (Flavor 6), Tally T 0 ((D+∑ i∈X,ZB i).val s) φ (R* ((G s)+(∑ i∈ X,V i s))) by
             have ht:=hv univ; rw[show lobbyR (i:=i) A d W H z a f z' s=G s+(∑ i:Flavor 6,V i s) from (by unfold lobbyR; simp only [Pi.add_apply,Finset.sum_apply]; rfl)] at h; exact consensus _ _ _ h _ ht
       intro X; induction X using Finset.induction_on with
       | empty=>simp only [sum_empty,add_zero]; exact hD
       | insert p X hp ih=>rw [sum_insert hp,sum_insert hp,add_comm (V p s),add_comm (ZB p), ← add_assoc D, ← add_assoc (G s), laysP]; exact Needle.totalY _ _ _ _ _ _ _ ih (hh p)
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.wool
#print axioms YM.Massive.Patria.Gall.Cahoots.orchid
