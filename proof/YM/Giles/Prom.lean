import YM.Giles.Felty
import YM.Giles.Foals
/-! Phys U extraction. Bond variation through moment stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
variable (T:TaperHol)(g:su.Color)(F P:Density c 6)(p:Flavor 6)(i j:Fiber)(a b:Axis)
-- row extraction.Weight exactly.W.
open Poised.Stative Poised.Display
local notation "Λ"=> (0:Multi 10)
set_option quotPrecheck false
local notation "U"=> (show SpinMode 10 from ((Λ,i),p))
local notation "V"=> (show SpinMode 10 from ((Λ,j),p))
local notation "L"=> reed p p i j (ballast Λ Λ T.T)
lemma every(X Y:SpinMode d)(P F:Density c 6)(J:Labels.Jet su)(h:ℝ) : uncoat (T.test d P F J h) X Y=(h:ℂ)^(spinWeight X.1.1+spinWeight Y.1.1) *∑ u:Site c,∑ v:Site c,Nw T.T X.1.1 u*Nw T.T Y.1.1 v * uncoat (foil P F (T.links c d J h)) ((u,X.1.2),X.2) ((v,Y.1.2),Y.2):=by
     let A:=T.links c d J h; let K:=uncoat (foil P F A); unfold TaperHol.test; rw [sectX]; rw [Matrix.mul_apply]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single X.1.2]; rw [sum_eq_single X.2]; rw [Matrix.transpose_apply, spin_slot,if_pos ⟨rfl,rfl⟩, Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type, Finset.mul_sum,Finset.mul_sum]; apply sum_congr rfl; intro j _; rw [sum_eq_single Y.1.2]; rw [sum_eq_single Y.2]; rw [spin_slot,if_pos ⟨rfl,rfl⟩,pow_add]; unfold foil; ring
     · intro a _ h; rw[spin_slot,if_neg (fun z=>h z.2)]; exact mul_zero _
     · simp
     · intro a _ h; apply sum_eq_zero; intro l _; rw[spin_slot,if_neg (fun z=>h z.1),mul_zero]
     · simp
     · intro a _ h; rw[Matrix.transpose_apply,spin_slot,if_neg (fun z=>h z.2),zero_mul]
     · simp
     · intro a _ h; apply sum_eq_zero; intro b _; rw[Matrix.transpose_apply,spin_slot,if_neg (fun z=>h z.1),zero_mul]
     simp
lemma escort (F:ℝ→ℂ) (hF:ContDiffAt ℝ (↑(10:ℕ):ℕ∞ω) F 0)(x:ℂ)(h:iteratedDeriv 4 F 0=(Nat.factorial 4:ℝ) • x): iteratedDeriv 10 (fun t:ℝ=> (t^6) • F t) 0=(Nat.factorial 10:ℂ) * x:=by
    let Q(t:ℝ):ℂ:=↑(t^6); change iteratedDeriv 10 (Q*F) 0= _; have hu:ContDiffAt ℝ (↑(10:ℕ):ℕ∞ω) Q 0:=Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_id.pow _)
    have hc(n:ℕ): iteratedDeriv n Q 0= ↑(if n=6 then (Nat.factorial 6:ℝ) else 0):=by
        unfold Q; rw [show (fun t:ℝ=> (↑(t^6):ℂ))= Complex.ofRealCLM ∘ fun t:ℝ=>t^6 from rfl, Display.clm_step (fun t:ℝ=>t^6) n 0 (contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero]; split; next h=> subst n; rfl
        next h=> simp
    rw [iteratedDeriv_mul hu hF,sum_eq_single 6]
    · rw [hc,if_pos rfl,show 10-6= (4:ℕ) from rfl,h]; norm_num [Nat.choose,Nat.factorial]; ring
    · intro i _ hi; rw [hc,if_neg hi]; simp
    norm_num
noncomputable def tiltX (p:Flavor 6)(i j:Fiber)(J:Labels.Jet su): Label 10→ₗ[ℂ]ℂ:= {
    toFun:=fun X=>Tawny.skin J (geometry 10 X.val) ((Λ,i),p) ((Λ,j),p), map_add':=fun x y=> by change (Tawny.skin J (geometry 10 (x.val+y.val))) ((Λ,i),p) ((Λ,j),p)=_; rw [map_add,map_add]; rfl, map_smul':=fun s x=>by change (Tawny.skin J (geometry 10 (s • x.val))) ((Λ,i),p) ((Λ,j),p) =_; rw [map_smul,map_smul]; rfl
    }
local notation "J★"=> leanY (legV g a b) 0
local notation "R"=>fling (c:=c) g T.T (legV g a b)
variable (X:Label 10)
lemma stood (hx: Tally T 0 X P F)(h: Along g (legV g a b))(ht:Chart 10 (foil P F) 1) : L (tent g (foil P F) R) = tiltX p i j J★ X:=by
    let H:=foil P F; let A:= H ∘ kiln g; let u:= R; let v: Cray c:= fling g T.T (0:Labels.Taylor su 1); let Y:=river u v
    have hX := collinear g 0 H (k:=10) (by rw [kiln0]; exact ht); have he :ContDiffAt ℝ (↑(10:ℕ):ℕ∞ω) (A ∘ Y) 0:= (show ContDiffAt ℝ (↑(10:ℕ):ℕ∞ω) A (Y 0) from (by unfold Y; rw[river0];exact hX)).comp _ ((river_c _ _).contDiffAt.of_le le_top)
    let M:=(reed (c:=c) p p i j (ballast Λ Λ T.T)).toContinuousLinearMap.restrictScalars ℝ; let K: SpinPol 10→ₗ[ℂ]ℂ:= { toFun:=fun x=>uncoat x U V,map_add':=fun x y=> congr_fun (congr_fun (map_add uncoat x y) U) V,map_smul':= fun i x=> congr_fun (congr_fun (map_smul uncoat i x) U) V }
    let G:= K.toContinuousLinearMap.restrictScalars ℝ
    let f:=T.test 10 P F J★; let gp:= fun t:ℝ=> observation 10 J★ t X.val
    have hT(t:ℝ): G (f t)= (t^6) • (M ((A∘Y) t)):=by
        change uncoat _ U V = _; unfold f; rw [every T U V P F J★, kicks g T _ _ t h (along0 g 1) (by decide)] -- rename g!
        rw [show spinWeight (U).1.1 + spinWeight (V).1.1 =6 from (by change spinWeight Λ+spinWeight Λ=_; rw [Tawny.Cast.Rays.gradeV]), ← Complex.ofReal_pow]; rfl
    have hp : SourceRead.Agrees f gp:=by rw [show gp= (desired X.val J★) from funext (observe J★ X.val)]; exact (stamps hx J★).2
    let x:= tent g H u; have hb:iteratedDeriv 4 (A ∘ Y) 0=(Nat.factorial 4:ℝ) • x:=by
        rw [money A hX (by omega) u v (by decide : 4 ≤ 10) (by decide :4<12)]; simp only [coin]; norm_num; rfl -- tricky A compose
    have h':iteratedDeriv 4 (M ∘ A ∘ Y) 0=(Nat.factorial 4:ℝ) • M x:=by rw [Display.clm_step _ _ _ (he.of_le (by norm_num)),hb,map_smul]
    have H:=escort (M∘A∘Y) (M.contDiff.contDiffAt.comp _ he) (M x) h'
    have ht: G ∘ f=(fun t:ℝ=> (t^6) • (M ((A ∘Y) t))):=funext hT
    apply mul_left_cancel₀ (show (Nat.factorial 10:ℂ)≠0 from by norm_num[Nat.factorial]); change (Nat.factorial 10:ℂ)*M x=(Nat.factorial 10:ℂ)*_
    rw [← H,show (fun t:ℝ=> t^6 • (M∘A∘Y) t) = _ from ht.symm, Display.clm_step _ _ _ hp.1,hp.2.2 10 le_rfl, show iteratedDeriv 10 gp 0= _ from Display.order_test X.val J★ 10]; exact map_smul K _ _
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.stood
