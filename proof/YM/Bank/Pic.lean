import YM.Bank.Ivo
/-! native coordinates at tested origin, Fourier reconstruction under real grid, estimates quantitative.Pick axial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Pic
open Gauge Function Filter Lattice Laurent Bloch Metric RG Precision Next.Free Finset
open Learn Glyph Plank Ivo Peak Kith Palm Jule Bee Pap Pilot Osc Cent Horse
open AnalyticBridge.LocalGaussianLaws.Current Matrix
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators ComplexConjugate
variable {g:Momentum→ℂ}{X:E4→ℂ}{k j i n:ℕ} {f:Side} {X':Bed}{w a t C e z:ℝ}
lemma solar (b A:ℝ)(he:0<e)(hk:k+7≤n)(hp:0<a)(h:Flute g X k)(σ:Bool):∃ C:ℝ,0 ≤ C∧∀ᶠ w:ℝ in atTop,∀ z:Cover, ((w^n)⁻¹ • rock z)∈Oasis e b→∀ᶠ c:Side in atTop,∀ f:Momentum→ℂ,Genie k σ c f g a A→ w*‖(w^n)^(k+3) • vote σ c z f - X ((w^n)⁻¹ • rock z)‖≤ C := by
    obtain ⟨L,H,ht,hU⟩:=h; obtain ⟨C,hc,h₀⟩:= Peak.tall hk hp ht H A b he σ
    refine ⟨C,hc,?_⟩; filter_upwards [h₀] with w hw z hz; filter_upwards [hw _ hz] with c hc f hf; rw [hU _ (door hz he)]; exact hc _ hf
section Gau
open Exterior Avalon Worth
local notation "θ"=> TypeFace 2

def glyph (H:Bed)(p q:PlaqAxes)(l r:List Axis)(x y:Cover)(n:Side):ℂ:= approached (rocker n θ l*learned H n*(rocker n θ r).transpose) (wrap n x,plaquette p) (wrap n y,plaquette q)
lemma solar_gauge (p q:PlaqAxes)(l r:List Axis)(x y:Cover) (hr: X'.metric.safe) (ht:Numeric (X'.metric.acts f) a C) (he:0<a):
   glyph X' p q l r x y f = vote false f (x-y) (spinWin l r fun w=> skyF X' w (plaquette p) (plaquette q)):=by
   let i:= plaquette p; let j:=plaquette q
   let G:= learned X' f; let L:= rocker f θ l; let R:= rocker f θ r; let U:= rotations f θ; let S:= solo f (skyF X'); let T:=stageVolume f; let Y:=approached R; let F:=approached L
   have hp: approached G=T⁻¹ •(U*S*Uᴴ):=by
        rw [← show approached G*U= _ from learns hr ht he, Matrix.mul_assoc, show U*Uᴴ= _ from (rotations_crew ..).2.1,Matrix.mul_smul,Matrix.mul_one, ← smul_assoc]; change _=(T⁻¹*T) • _; rw [inv_mul_cancel₀ (stage_ne _),one_smul]
   have hx(s):star (cell s (wrap f y)) = mode (mon s) (-y):=by rw [cell_wrap,← mode_adjoint (mon s),show star (mon s)=_ from real_frequency s] -- check
   have hu : approached (L*G*R.transpose)= T⁻¹ • ((F*U)*S*(Y*U)ᴴ):=by
      rw [prom_mul,prom_mul,prom_adj,hp,Matrix.mul_smul,Matrix.smul_mul,Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]; rfl
   unfold glyph; rw [show (approached _) _ _= _ from congr_fun (congr_fun hu (wrap f x,i)) (wrap f y,j), Matrix.smul_apply]; unfold vote summit
   rw [show T⁻¹=(((f.val:ℝ)⁻¹^4:ℝ):ℂ) from (by unfold T stageVolume; push_cast; ring), smul_eq_mul,←Complex.real_smul]; congr 1
   rw [mul_apply,Fintype.sum_prod_type]; refine sum_congr rfl fun s _=> ?_
   rw [sum_eq_single j]
   · rw [mul_apply, Fintype.sum_prod_type,sum_eq_single s]
     · rw [sum_eq_single i]; unfold F Y L R U S; rw [rock_same,conjTranspose_apply,rock_same]; simp only [solo,fiber, Matrix.of_apply,rotations,if_true]; rw [star_mul,stars_back _ _ (mon_mem _ _).1,hx,cell_wrap, sub_eq_add_neg,mode_shift]; change _ = mode (mon s) x*mode (mon s) (-y)*(skyF X' (mon s) i j*listChip (mon s) l*listChip (-mon s) r); ring
       intro d _ hd; unfold F L U; rw [rock_same]; simp [rotations,hd,Ne.symm hd]; simp
     intro d _ hd; apply sum_eq_zero; intro y _; unfold S; simp [solo,fiber,hd]; simp
   · intro y _ hy; unfold Y R U; rw [conjTranspose_apply,rock_same]; simp [rotations,hy,Ne.symm hy]
   simp

def stove (T:E4→ℂ)(l r:List Axis):=(-1:ℂ)^r.length • earn r (earn l T)
lemma calf (he:0<e)(b:ℝ)(a t M:ℝ)(ha:0<a)(ht:0<t)(hm:0≤M)(p q:PlaqAxes)(l r:List Axis)(hn:1+l.length+r.length+7≤n): ∃ C:ℝ,0≤ C ∧∀ᶠ w:ℝ in atTop,∀ z:Cover, ((w^n)⁻¹ • rock z)∈Oasis e b→ ∀ᶠ c:Side in atTop,∀ (H:Bed),H.metric.strip t M→Numeric (H.metric.acts c) a M→H.metric.read 0=1→ ∀ x y:Cover,x-y=z →
     w*‖(w^n)^(4+l.length+r.length) • glyph H p q l r x y c -stove (from_p p q) l r ((w^n)⁻¹ • rock z)‖≤ C:=by
   obtain ⟨s,C,hs,hc,G⟩:=gaugeW a M t ha hm ht; obtain ⟨A,hA,W⟩:= turbo hc l r (a:=s)
   have hv := Flute.functions l r (kettle p q)
   obtain ⟨B,hB,H⟩:=solar b A he hn hs hv false; refine ⟨B,hB,?_⟩; filter_upwards [H] with u hu z hx; filter_upwards [hu z hx] with c hc1 P hp ht' hz x y hy; rw [solar_gauge _ _ _ _ _ _ (Row.rights _ _ hp ht.le) ht' ha,hy]
   rw [show 4+l.length+r.length = 1+l.length+r.length+3 by omega]; exact hc1 _ (W _ _ _ _ _ (G _ hp ht' hz _ _))
end Gau
open QCD QCD.Lat QCD.Free QCD.Flume
open Pearl
-- periodic seam compatible cut for spins. Adj matrix picks
private lemma echo_spin (D:Sheet f)(v:List Axis): oldDiff D v=oldDiff (1:Sheet f) v*D:=by induction v with
    | nil=>simp[oldDiff]
    | cons a v ih=> rw [oldDiff,oldDiff,ih]; unfold after; rw [Matrix.mul_assoc]
private lemma rose (v:List Axis)(x:Site f)(p:Site f)(a b:Fiber): (oldDiff (1:Sheet f) v*leaf f) (x,a) (p,b)=listChip (tuning p) v*scarf p x*(1: Bundle) a b:=by
    induction v generalizing x with
    | nil=> simp only [oldDiff,listChip,List.map_nil,List.prod_nil,one_mul]; rfl
    | cons i v ih=> rw [oldDiff, show after _ _ * leaf f= after (oldDiff (1:Sheet f) v*leaf f) i from Matrix.mul_assoc .., afterwards,ih,ih]; have hx:= scarf_a p x i; rw [Exterior.factor] at hx; change _= chip (tuning p i)*listChip (tuning p) v*scarf p x* _; unfold chip; linear_combination ((listChip (tuning p) v)*(1:Bundle) a b)*hx
def Sway (p:Train j)(n:Side)(v u:Fiber)(x y:Cover) (l r:List Axis) := occ (0:Site n) x*occ (0:Site n) y*(oldDiff (1:Sheet n) l*stage p n*(oldDiff (1:Sheet n) r)ᴴ) (wrap n x,v) (wrap n y,u) -- standard in chart origin 0. Moves to AP coefficient at shift.Tr.App.
lemma solar_spiral (p:Train j)(n:Side)(v u:Fiber)(x y:Cover)(l r:List Axis):
    Sway p n v u x y l r = vote true n (x-y) (spinWin l r fun q=> vase (Flume.Dir p) q v u):=by
    have hx (i:Site n)(x:Cover): occ (0:Site n) x *scarf i (wrap n x)=(n.val:ℂ)⁻¹^2 *mode (tuning i) x:=by rw [show scarf i (wrap n x)=scarf i (0+wrap n x) from congr_arg _ (zero_add _).symm, concord, wave_root i 0]; congr 1; simp [mode, rep]
    have hm(y:Cover):star (occ (0:Site n) y)=occ (0:Site n) y:=(realSeam (0:Site n) _).1
    have hb i: star (mode (tuning (n:=n) i) y)=mode (tuning i) (-y):=by
         rw [←mode_adjoint, show star (tuning i)=_ from (keyboard i).1]
    unfold Sway stage vote summit
    rw [QCD.Bank.fiberSum, mul_sum, Finset.smul_sum]; apply sum_congr rfl; intro i _
    rw [sum_eq_single u, sum_eq_single v]
    · rw [rose,rose, Matrix.one_apply_eq,Matrix.one_apply_eq,mul_one,mul_one, QCD.Bank.comes_g] -- edit
      let α:=listChip (tuning i) l; let β:= listChip (tuning i) r
      let Z:= vase (Flume.Dir p) (tuning i) v u; let R:=(n.val:ℂ)⁻¹^2
      calc
         _ = α*(occ (0:Site n) x*scarf i (wrap n x))*Z* star (β*(occ (0:Site n) y*scarf i (wrap n y))):=by simp only [star_mul,hm]; unfold Z α β; ring
         _ = _:=by rw [hx,hx]; change _=(n.val:ℝ)⁻¹^4 • (mode (tuning i) (x-y) * (Z*α*listChip (-tuning i) r)); rw [sub_eq_add_neg,mode_shift,Complex.real_smul]; unfold β; rw [star_mul,star_mul,hb,stars_back _ _ (keyboard i).1]; push_cast; simp; ring
    · intro w _ he; rw [rose]; simp[Matrix.one_apply,he, Ne.symm he]
    · simp
    · intro w _ he; apply sum_eq_zero; intro k _; rw [rose r]; simp[Matrix.one_apply,he,Ne.symm he]
    simp
lemma pence (he:0<e)(b:ℝ)(j:ℕ) (hj:2≤j)(p q:Fiber)(l r:List Axis)(hn:l.length+r.length+7≤n): ∃ C:ℝ,0 ≤ C ∧∀ᶠ w:ℝ in atTop,∀ z:Cover, ((w^n)⁻¹ • rock z)∈Oasis e b →∀ᶠ c:Side in atTop,∀ D: Train j,∀ x y:Cover,x-y=z →
    w*‖(w^n)^(3+l.length+r.length) • Sway D c p q x y l r -stove (s_k p q) l r ((w^n)⁻¹ • rock z)‖ ≤ C:=by
   obtain ⟨s,C,hs,hc,G⟩:= QCD.Bank.spineW hj; obtain ⟨A,hA,W⟩:= turbo hc l r (a:=s)
   have hv := Flute.functions l r (vista p q)
   obtain ⟨B,hB,H⟩:=solar b A he (show 0+l.length+r.length+7≤n by omega) hs hv true; refine ⟨B,hB,?_⟩; filter_upwards [H] with u hu z hx; filter_upwards [hu z hx] with c hc1 P x y hy; rw [solar_spiral,hy]
   rw [show 3+l.length+r.length = 0+l.length+r.length+3 by omega]; exact hc1 _ (W _ _ _ _ _ (G _ _ _ _))
end YM.Bank.Pic
#print axioms YM.Bank.Pic.calf
#print axioms YM.Bank.Pic.pence
