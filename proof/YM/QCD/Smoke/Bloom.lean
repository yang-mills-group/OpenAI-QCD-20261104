import YM.QCD.Smoke.Board

/-! # anchor letter paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Push.Uniform Run Tree RG
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Sparks Jacobi Extra Iteration Work.F03
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n N: Side} {r C d:ℝ}{M:Cnr n→ ℝ}
abbrev Wisp:= Fin 2→ Stock
def triangleG (k:Wisp)(x:Fin 2→ su.ColorIndex):Kite:= fun i=> ((k i).1,(k i).2,x i)
def stroke (k:Wisp):=∑ i,Laurent.size (k i).1
def reedG (P:Planet)(k:Wisp)(x:Fin 2→su.Color):ℝ:= ∑ q,P (triangleG k q)*∏ i,x i (q i)
lemma suitG {M :Cnr n →ℝ} (k:Wisp)(b:Fin 2→su.ColorIndex)(hp:AtMap n (exposed (triangleG k b)))(x:Fin 2→su.Color): reedG (scene M) k x=scanG M (palette (0,k) n x):=by
  have hm q: scene M (triangleG k q)=entry M 0 (chartB (triangleG k q)):=if_pos ((rub (p:=(0,k)) b q).1 hp)
  let p:=palette (0,k) n x; unfold scanG; rw [show palette (0,k) n x=(fun i=>∑ j:su.ColorIndex,x i j • Push.Uniform.bolt (wrap n (k i).1,(k i).2,j)) from funext fun _=>hybrids .., blast]; unfold reedG; apply sum_congr rfl; intro i _; rw [hm,mul_comm]; exact ((iteratedFDeriv ℝ 2 M 0).toMultilinearMap.map_smul_univ _ _).symm -- inspect
lemma glowQ (h: Cigar M r C)(k:Wisp)(x:Fin 2→su.Color)(u:su.El): reedG (scene M) k (fun i=> su.adjoint u (x i))= reedG (scene M) k x :=by
  by_cases hp:∃ b, AtMap n (exposed (triangleG k b))
  · obtain ⟨b,hp⟩:=hp; rw [suitG k b hp,suitG k b hp,show palette (0,k) n (fun i=> _)=(stain u ∘ palette (0,k) n x) from funext fun _=> (stained_lock u ..).symm,cargo h ..] -- tactic
  unfold reedG scene; push Not at hp; simp only [if_neg (hp _),zero_mul]
variable {S:SparkMesh}{T:Skyline S}{P:Planet}{m:ℕ→ℕ}
lemma atmosphere (h:∀ i, Cigar (T i) r C)(hp: Heaven S T (r/4) C P m)(k:Wisp)(x: Fin 2→su.Color)(u:su.El): reedG P k (fun i=>su.adjoint u (x i))=reedG P k x:=by
  have he x:Tendsto (fun j=> reedG (scene (T (m j))) k x) atTop (𝓝 (reedG P k x)):= tendsto_finsetSum _ fun i _=> (hp.converges _).mul_const _
  apply tendsto_nhds_unique (he (fun i=> su.adjoint u (x i))); simp_rw [fun i=> glowQ (h _) k x u]; exact he x
abbrev Wink (i:Wisp):= Ryde ((0,i) : Rim 2)
abbrev Twig := (i:Wisp) × Wink i
def strata (P:Planet)(i:Twig):Atom su 2:={ leg:=fun a=> shop (plant (i.1 a) (i.2 a)), coeff:=fun a=> signal (0,i.1) i.2 * P (triangleG i.1 a) }
lemma roadSale (P:Planet)(p:Twig): (strata P p).length≤2*stroke p.1+12:=by
  have hu:=cost_pays (k:=2) ((0,p.1):Rim 2) p.2 (0:Typewriter 2)
  simp only [Bloom.span,rivet,cost,rad_length,show Laurent.size (0:Cover)=0 from by simp [Laurent.size],zero_add] at hu; exact hu
lemma soldSym (h:∀ i,Cigar (T i) r C)(he: Heaven S T (r/4) C P m)(i:Twig): (strata P i).Invariant:=by
  intro u x; unfold Atom.poly; simp only [strata]; simp_rw [mul_assoc,← Finset.mul_sum]; exact congr_arg (signal (0,i.1) i.2*·) (atmosphere h he ..)
lemma soldQty (p:Wisp): (Fintype.card (Wink p):ℝ)≤(2*stroke p+2)^4:=by
  have he := cost_count (k:=2) (0,p); rw [show cost (0,p)=stroke p from by simp [cost,stroke,Laurent.size]] at he; exact he
def steamG (r D:ℝ):ℝ:= Real.exp (12*r)*((Fintype.card (Fin 2→ su.ColorIndex):ℝ)*D)
def steamH (r D:ℝ):ℝ:= 16*momentPrice 4 r*steamG r D
lemma soldCost (he: Heaven S T r C P m)(hd:4*d≤r)(hh:0<d)(hC:0≤C)(i: Twig): (strata P i).budget d ≤ steamG d C * Real.exp (-(2*d)*stroke i.1) :=by
  have hF b : timbre (exposed (triangleG i.1 b))=stroke i.1:=by unfold timbre exposed triangleG stroke; simp [Laurent.size]
  have hx j : |(strata P i).coeff j| ≤ C*Real.exp (-r*stroke i.1):=by
    unfold strata; rw [abs_mul]; apply (mul_le_of_le_one_left (abs_nonneg _) (revenue ..)).trans; have ht := he.ceiling (triangleG i.1 j); rw [flown,aim,hF] at ht; exact ht
  have ht := sum_le_sum (s:=univ) fun j _=>hx j; rw [sum_const,card_univ,nsmul_eq_mul] at ht
  apply (mul_le_mul ht (Real.exp_monotone (show d*((strata P i).length:ℝ) ≤ d*(2*stroke i.1+12) from mul_le_mul_of_nonneg_left (by exact_mod_cast roadSale P i) hh.le)) (Real.exp_pos _).le (by positivity)).trans
  rw [mul_assoc _,mul_assoc C,← Real.exp_add]; unfold steamG; -- check
  let z:ℝ:= (Fintype.card (Fin 2→su.ColorIndex):ℝ); let a:ℝ:=stroke i.1; have ha:0 ≤ a:=by unfold a; positivity
  calc
    _ ≤ z*(C*Real.exp (12*d + -(2*d)*a)):=by unfold z a; apply mul_le_mul_of_nonneg_left _ (by positivity); apply mul_le_mul_of_nonneg_left _ hC; apply Real.exp_monotone; unfold a at ha; nlinarith
    _ = _:=by rw [Real.exp_add]; unfold a z; ring

def fogP (p:Wisp)(r:ℝ):= Real.exp (-r*stroke p)
lemma fogBill (he:0<r): Summable fun p:Wisp=>fogP p r:=by
  have hp : Injective (fun p:Wisp=>((0,p):Rim 2)):=fun _ _ h=>congr_arg Prod.snd h
  have hx p : tab ((0,p):Rim 2) r=fogP p r:=by unfold tab fogP; rw [show cost (0,p)=stroke p from by simp [stroke,cost,Laurent.size]]
  simp_rw [← hx]; exact (cost_can 2 he).comp_injective hp

def auction (r C:ℝ):=steamH r C*(∑' i: Wisp,fogP i r)
lemma steam_pos (hp:0 ≤ C)(hr:0<r):0≤ steamG r C:=by unfold steamG; positivity
lemma steam_h (hp:0 ≤ C)(hr:0<r):0≤steamH r C:=by unfold steamH; have hh:=momentPrice_pos 4 hr; have hx:=steam_pos hp hr; positivity
lemma auction_pos (hp:0≤ C)(hr:0<r):0 ≤ auction r C := mul_nonneg (steam_h hp hr) (tsum_nonneg fun i=> (Real.exp_pos _).le)
lemma sold (he:Heaven S T r C P m)(hd:4*d≤r)(hh:0<d)(hC:0≤C): Charged (strata P) d (auction d C):=by
  refine Cost.sigma (Cost.scale (α:=Wisp) ⟨fun i=>(Real.exp_pos _).le, fogBill hh,le_rfl⟩ (steamH d C) (steam_h hC hh)) (fun i=> Cost.enlarge (Cost.mono (Cost.finite (α:=Wink i) (steamG d C * Real.exp (-(2*d)*stroke i)) (mul_nonneg (steam_pos hC hh) (Real.exp_pos _).le)) (fun j=> by unfold Atom.budget Atom.magnitude; positivity) (fun j=>soldCost he hd hh hC ⟨i,j⟩)) ?_)
  let a:ℝ:=stroke i; have ha:0≤a:=by unfold a; positivity
  have he : (2*stroke i+2:ℝ)^4 ≤16*(momentPrice 4 d * Real.exp (d*a)):=by
    apply le_trans (le_of_eq (show (2*(↑(stroke i):ℝ)+2)^4=16*(1+a)^4 by unfold a; ring)); gcongr; exact spendMoment 4 hh ha
  apply (mul_le_mul_of_nonneg_right ((soldQty i).trans he) (mul_nonneg (steam_pos hC hh) (Real.exp_pos _).le)).trans_eq; unfold steamH; unfold a
  rw [show (-(2*d))*(stroke i:ℝ)= -(d*stroke i)+ -d*stroke i by ring,Real.exp_add,Real.exp_neg]; field_simp -- exp inverse
end YM.QCD.Smoke
