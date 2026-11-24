import YM.QCD.Kites.Alone
import YM.Massive.Filament.Diamond

/-! # Coeff prices in currency `Quits`.

No occupancy cost thrown away; this is needed to pay the new slots at Ω without
interchanging the optimum U & V with the sum. For K cost tolerance μ variant, spent at each Volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open Massive.Filament
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N B:ℕ}{h A R C D W r:ℝ}{s z:ℂ} {ι α: Type}
variable (X: ℂ → ℂ → Rail c N ι)
variable {P:ι→Grid c→ℂ→ℂ→EvenA c N}{x:Site c}
-- Lantern bulbs. hypothesis implies local measurable gauge etc separately. Use this at each transfer before projection.
structure Arc : Prop where
 brace (z s:ℂ): (X z s).addr=(X 0 0).addr
 reading (i:ι)(U:Grid c) : Fused (fun z s=> (X z s).warp i U)
def joule (h:ℝ) : EvenA c N →L[ℂ] Alg (Keys c N):= by
    letI : FiniteDimensional ℂ (Patio (Keys c N)):= FiniteDimensional.of_injective (light (Keys c N)).toLinearMap (fun _ _=>Subtype.ext)
    exact LinearMap.toContinuousLinearMap (((Grass.changeVars (Matrix.diagonal (fun _:Keys c N=>(h:ℂ)))).comp (light (Keys c N))).toLinearMap)
set_option quotPrecheck false
local notation "X₀"=> X 0 0
lemma J_of (v:EvenA c N) : token c N h v= joule (h:=h) v:=rfl
open Ruby Fused

def fuelCharge (G:Rail c N ι)(B:ℕ) (R A:ℝ)(x: Site c)(i:ι):= if x∈ Ruby.home G i then R^(oriD G i).card *Real.exp (A * coverNumber B (Ruby.home G i)) else 0
variable {J β : Type}
lemma fuelHit (X:Rail c N J) (p:J→ℝ): Ac.Hit (Ruby.home X) B (GasP.taxed (oriD X) p R) A C ↔ ∀ x,SumBudget (fun i=> fuelCharge X B R A x i*p i) C:=by
   have hv (x): (fun i=> fuelCharge X B R A x i*p i)=(fun i=>if x∈ Ruby.home X i then taxed (oriD X) p R i*Real.exp (A*coverNumber B (Ruby.home X i)) else 0):=by
      funext i; unfold fuelCharge; split <;> first | exact zero_mul _| unfold taxed; ring
   simp_rw [hv]; rfl
lemma fpos (X:Rail c N J)(x: Site c)(hr:0≤R): 0 ≤ fuelCharge X B R A x:= by intro i; change 0 ≤ fuelCharge X B R A x i; unfold fuelCharge; split <;> first | exact le_rfl| positivity
lemma fray (X:Rail c N J)(p:ι→J)(i:ι) (hr:0<R): ∃ x,0<fuelCharge X B R A x (p i) := by
   obtain ⟨t,ht⟩:= (X.addr (p i)).alive; refine ⟨t,?_⟩; rw [fuelCharge,if_pos (show t∈ Ruby.home X (p i) from (X.addr _).part ht)]; positivity

def beadK (n:ℕ)(s:ℂ): Rail c N ι :=⟨(X 0 0).addr,fun i U=> bead n (fun z=>(X z s).warp i U)⟩
lemma Arc.beam {n:ℕ}(hp:Arc X)(hB:∀ (z s:ℂ), ‖z‖<1→‖s‖<1 → Quits (X z s) B C R A h)(hr:0<R)(hv:0< r)(hz:r<1)(hn:n≠0)(hs: Safe s): Quits (beadK X n s) B (2*(luster C (peso n) s/r^n)) R A h := by
   let T:= beadK X n s; let b(x):=fuelCharge (X 0 0) B R A x; let c₀:= luster C (peso n) s/r^n; let K:=joule (c:=c) (N:=N) (h:=h)
   have hh : ∀ (x:Site c)(S:Finset ι)(Y:ι→Grid c),∑ i∈S, b x i*‖K (T.warp i (Y i))‖≤ c₀:=by
      intro x S Y; let H i z s:= K ((X z s).warp i (Y i)); have hU i (V:Grid c): Fused (fun z s=> K ((X z s).warp i V)):= (hp.reading i V).compose K K.contDiff
      have ht i: K (T.warp i (Y i))= bead n (fun z=> H i z s):=(handset n K ((hp.reading i (Y i)).wire _ (withinL hs)) zero_lt_one).symm; simp_rw [ht]; apply emerald (fun i=>hU i (Y i)) (fpos _ _ hr.le) ?_ hv hz hs _ hn
      intro z s h₁ h₂; obtain ⟨g,hg,hϕ⟩:= (hB z s h₁ h₂).cost
      have hA' x: fuelCharge (X z s) B R A x=b x:=by unfold b fuelCharge oriD Ruby.home; rw [hp.brace]
      have hF := (fuelHit (X z s) g).mp hg x; rw [hA'] at hF; exact (sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (show ‖H i z s‖ ≤g i from hϕ i _) (show 0≤b x i from fpos _ _ hr.le i)).trans (budget_sum hF S)
   let F i (V:Grid c):= ‖K (T.warp i V)‖
   have hw(i:ι):BddAbove (Set.range (F i)):=by
       obtain ⟨x,hx⟩:=fray (A:=A) (B:= B) X₀ id i hr; refine ⟨c₀/b x i,fun _ h=>?_⟩; obtain ⟨y,rfl⟩:=h; exact (le_div_iff₀ hx).mpr (by unfold F; rw [mul_comm]; change b x i* ‖K (T.warp i y)‖≤ c₀; have ho:= hh x {i} (fun _=>y); rw [sum_singleton] at ho; exact ho)
   choose Y hY using (fun i:ι=>almost_sup (1:Grid c) (fun _=>norm_nonneg _) (hw i))
   let y i:=F i (Y i); refine ⟨fun i=>2*y i, (fuelHit T _).mpr fun x=> ?_, fun i U=>hY i U⟩
   refine budget_of_sum (fun i=>mul_nonneg (fpos _ _ hr.le _) (mul_nonneg (by norm_num) (norm_nonneg _))) fun S => le_trans ?_ (mul_le_mul_of_nonneg_left (hh x S Y) (by norm_num : (0:ℝ) ≤2))
   refine le_of_eq ?_; rw [mul_sum]; exact sum_congr rfl (fun i _=>show b x i*(2*y i)=2*(b x i*y i) from mul_left_comm ..)
variable {u q D':ℝ}
def watt (X:Rail c N ι)(u:ℂ): Rail c N ι:=⟨X.addr,fun i v=>u • X.warp i v⟩
def kaX (Q:α→Rail c N ι): Rail c N (α×ι):= ⟨fun p=> (Q p.1).addr p.2,fun p=> (Q p.1).warp p.2⟩
def faint (n:ℕ)(u:ℝ)(s:ℂ) : Rail c N ι:= watt (beadK X n s) (u^n:ℂ)
def tail (u:ℝ) (s:ℂ) : Rail c N (ℕ × ι) := kaX (fun n:ℕ=> faint X (n+2) u s)
def beamPay (C S q:ℝ) (s:ℂ):ℝ:= (2*luster C 3 s)*(1-q/S)⁻¹
lemma watt_price (X: Rail c N ι)(u:ℂ)(hp: Quits X B C R A h): Quits (watt X u) B (‖u‖*C) R A h:=by
   obtain ⟨f,hf,he⟩:=hp.cost; refine ⟨fun i=> ‖u‖*f i,(fuelHit _ _).mpr fun x=>?_, fun i V=>?_⟩
   · have hx: (fun i=>fuelCharge (watt X u) B R A x i*(‖u‖*f i))=(fun i=> ‖u‖*(fuelCharge X B R A x i*f i)):=funext fun i=> show _=_ from mul_left_comm ..; rw [hx]; exact budget_scale (norm_nonneg _) ((fuelHit _ _).mp hf x)
   let L:=joule (c:=c) (N:=N) (h:=h); change ‖L (u • X.warp i V)‖ ≤ _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (he i V) (norm_nonneg _)
lemma wattsLoosen (X: Rail c N ι)(hp:Quits X B C R A h)(he:C≤D): Quits X B D R A h:=by obtain ⟨f,hf,h⟩:=hp.cost; exact ⟨f,fun i=>budget_loosen (hf i) he,h⟩
lemma bunch (Q:α→Rail c N ι)(c':α→ℝ)(hp:∀ i,Quits (Q i) B (c' i) R A h)(hg:SumBudget c' C):Quits (kaX Q) B C R A h:=by
   choose f hf he using fun i=> (hp i).cost; let F (p:α×ι):= f p.1 p.2; refine ⟨F,(fuelHit _ _).mpr fun x=> budget_rows (fun i=>fuelCharge (kaX Q) B R A x i* F i) c' (fun i=> (fuelHit _ _).mp (hf i) x) hg, fun p U=>he _ _ _⟩
lemma Arc.hawk (hp:Arc X)(hB:∀ (z s:ℂ), ‖z‖<1→‖s‖<1 → Quits (X z s) B C R A h)(hr:0<R)(hs:Safe s)(hv:0≤u)(hu:u<r)(hz:r<1):
   Quits (faint X 1 u s) B (2*luster C 2 s) R A h ∧ Quits (tail X u s) B (beamPay C r u s) R A h:=by
     let g:=u/r; have hj:= lt_of_le_of_lt hv hu; have he:0≤ C:= by obtain ⟨f,h₀,_⟩:= (hB 0 s (by simp) (withinL hs)).cost; exact budget_nonneg (h₀ 0)
     have hg:0≤g:=div_nonneg hv hj.le; have hh:g<1:= (div_lt_one hj).mpr hu
     have hh'(n:ℕ)(hi:n≠0): Quits (faint X n u s) B ((2*luster C (peso n) s)*g^n) R A h:= by
         have hx:= watt_price _ (u^n:ℂ) (hp.beam X hB hr hj hz hi hs)
         unfold g faint; convert hx using 1; rw [div_pow, norm_pow,Complex.norm_real,Real.norm_of_nonneg hv]; ring -- syntax
     refine ⟨wattsLoosen _ (hh' 1 (by omega)) ?_,bunch _ (fun i:ℕ=>2*luster C 3 s*g^i) (fun i=> wattsLoosen _ (hh' (i+2) (by omega)) ?_) (budget_geometric ?_ hg hh)⟩
     · rw [peso,if_pos rfl]; exact mul_le_of_le_one_right (mul_nonneg (by norm_num) (Fused.lucre 2 he)) (by rw [pow_one]; exact hh.le)
     · rw [peso,if_neg (by omega)]; rw [pow_add]; refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (pow_nonneg hg _) (by apply pow_le_one₀ hg hh.le)) (mul_nonneg (by norm_num) (lucre 3 he))
     exact mul_nonneg (by norm_num) (Fused.lucre 3 he)
lemma watt_press (X:Rail c N ι)(δ:ℝ)(h1:0<q)(h2:0<R)(h3:1 ≤ R)(hp:Quits X B C (q*R) A h)(hb: C ≤ δ*R) : Quits X B δ q A h:=by
    obtain ⟨f,hf,hM⟩:=hp.cost; refine ⟨f,(fuelHit _ _).mpr fun x=> ?_, hM⟩
    refine budget_loosen (D:=δ) (budget_mono (budget_scale (inv_nonneg.mpr h2.le) ((fuelHit X f).mp hf x)) (fun i=>mul_nonneg (fpos _ _ h1.le _) ((norm_nonneg _).trans (hM i 1))) ?_) ?_
    · intro i; have ht:(oriD X i).card≠0:= (card_pos.mpr (X.addr i).alive).ne'; unfold fuelCharge; split
      next h=> rw [mul_pow]; have hz:R⁻¹ * R^(oriD X i).card ≥ 1:=by rw [inv_mul_eq_div]; exact (one_le_div h2).2 (le_self_pow₀ h3 ht)
               have he:=le_mul_of_one_le_left (mul_nonneg (mul_nonneg (pow_nonneg h1.le (oriD X i).card) (Real.exp_pos (A*coverNumber B (Ruby.home X i))).le) ((norm_nonneg _).trans (hM i 1))) hz
               exact le_trans he (le_of_eq (by ring))
      next _=> simp
    rw [inv_mul_eq_div]; exact (div_le_iff₀ h2).mpr hb

end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.Arc.beam
#print axioms YM.QCD.Fibre.Arc.hawk
