import YM.MassiveQCD.Mayer.Sprouts
import YM.MassiveQCD.Mayer.Laws
import YM.MassiveQCD.Mayer.Stamp
/-! # Priceable Mayer shutters
 Cents at every received `x`. Must keep the entire exponent on all the new rays and all the
 unmasked values (including ℂ values) and symmetries in applying to a Path. Inputs at
 valuation with `merit` per marker not per extent. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Reggae
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {c:Side}{N:ℕ}{o:Site c}{B:Support c}{t q a r:ℝ}{k n:ℕ}
local notation "Z"=>EvenA c N
local notation "Q"=>Sen (N:=N) o t
open MassiveQCD.Analysis MassiveQCD.Analysis.Many
variable {V:Config su c}{f g:Grid c→EvenA c N}{p:BudgetPoint}{D:Directions su c→Prop}
noncomputable def braid (f:Grid c→EvenA c N) (v:ℂ)(l:Rays): Grid c → EvenA c N:= fun x => grow (v • f x) l
noncomputable def plyM (f:Grid c→EvenA c N) (v:ℂ)(l:Rays): Grid c→ EvenA c N := logM ∘ braid f v l
lemma braid_advance (z:ℂ)(j:ℕ)(k:Rays): braid f z (j::k)= (-coeffM (j+2)) • ((braid f z k)^(j+2)):= by funext i; rw [Pi.smul_apply,Pi.pow_apply]; rfl
local notation "R"=>p.order
variable (zz:ℂ)(ht:1≤t)(h:Woven o B p t f a)(hp:2^p.order*a≤1/4)(hZ:‖zz‖≤1)
include h hp ht hZ
lemma brood (l:Rays): Woven o B p t (braid f zz l) (Many.vigor l*a):=by
    have he:=h.travel
    induction l with
    | nil=> exact (complexTone h zz).stretches (Subset.refl _) (mul_le_mul_of_nonneg_right hZ he)
    | cons j k ih=>
       rw [braid_advance]; let u:= Many.vigor k*a; have hx:0≤u:=mul_nonneg (Many.tack k).2.1.le he; have hA:u≤a:= mul_le_of_le_one_left he (Many.tack k).2.2
       apply ((payPower (zero_lt_one.trans_le ht) (j+1) ih).byScalar _).stretches (Subset.refl _); rw [norm_neg]; change ‖coeffM _‖* ((2^p.order*u)^(j+1)*u) ≤ (wagon j*Many.vigor k)*a; rw [mul_assoc (wagon j)]; exact (mul_le_mul ((horizon ..)) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity :0≤(2:ℝ)^p.order*u) ((mul_le_mul_of_nonneg_left hA (by positivity :0≤(2:ℝ)^p.order)).trans hp) _) hx) (by positivity) zero_le_one).trans_eq (one_mul _)
omit ht hZ in
lemma holdsU (l:Rays): Many.vigor l*a ≤1/4:=by
     apply (mul_le_of_le_one_left h.travel (Many.tack l).2.2).trans; exact (le_mul_of_one_le_left h.travel (one_le_pow₀ (by norm_num))).trans hp
lemma braidLaw (l:Rays): let b:=Many.vigor l*a; Woven o B p t (plyM f zz l) (logFee (p.order)*b) ∧ ∀ V:Grid c,Healthy p.threshold B V → ‖braid f zz l V‖≤ b:=by
    intro b; have he:= brood zz ht h hp hZ l; refine ⟨log_budget ht he ?_, fun V hV=> ((pass_high _ ht (o:=o)).trans (he.sizeU V hV))⟩; exact (holdsU h hp l).trans (by norm_num)
lemma lantern (V:Grid c): let u l:= masked p.threshold B (plyM f zz l) V; HasSum u (zz • masked p.threshold B f V):=by
    intro u; by_cases hV: Healthy p.threshold B V; swap
    · have hv (l):u l=0:= masked_ne _ _ _ _ hV; rw [masked_ne _ _ _ _ hV,smul_zero,funext hv]; exact hasSum_zero
    rw [masked_eq _ _ _ _ hV]; apply HasSum.congr_fun (f:=fun l=> plyM f zz l V) _ (fun l=> masked_eq _ _ _ _ hV)
    let x:= zz • f V; have he i: grow x i=braid f zz i V:=rfl; have hf(i):= (braidLaw zz ht h hp hZ i).2 V hV
    let τ(l):=Many.vigor l*a; have hH : Summable τ:= Many.purse.2.1.mul_right a
    have hX : Summable (grow x):= Summable.of_norm_bounded hH hf
    have h0 : Summable fun i=> logM (grow x i):= Summable.of_norm_bounded (hH.mul_left (logFee p.order)) fun i=> (pass_high _ ht (o:=o)).trans ((braidLaw zz ht h hp hZ i).1.sizeU _ hV) -- shadow
    exact blooming hX h0 (fun i=>(he i) ▸ ((hf i).trans_lt (lt_of_le_of_lt (holdsU h hp i) (by norm_num)))) -- types
omit h hp ht hZ
lemma braid_homo (z:ℂ)(l:Rays): braid f z l= z^Many.tier l • braid f 1 l:=by
    induction l with
    | nil=> rw [show Many.tier []=1 from rfl,pow_one]; exact funext fun i=> congr_arg (z • ·) (one_smul ℂ (f i)).symm
    | cons j k ih=> rw [braid_advance,braid_advance,ih,Many.tier,mul_comm (j+2),pow_mul]; simp only [smul_pow]; exact smul_comm ..
lemma growR (u:Z →+* Z)(hp:Continuous u)(x: Z)(l:Rays): u (grow x l)=grow (u x) l:=by
    induction l with
    | nil=> rfl
    | cons j k ih=> rw [grow,grow, Many.branch, eSM u hp,map_pow,ih]; rfl
lemma plies (Y:Z→+*Z)(h:Continuous Y)(hp:Bijective Y){A U:Grid c}(he:Y (zz • f U)=zz • g A)(l:Rays): Y (plyM f zz l U)=plyM g zz l A:=by
    unfold plyM braid; rw [comp_apply,comp_apply,log_honors _ h hp, growR _ h, he]
lemma coloredLog (z:ℂ)(h:shadeG f)(l:Rays): shadeG (plyM f z l):=by
    intro U k; let F:=Lat.rotates N k; refine congr_arg Subtype.val (plies z (sways F) (phare _) (surfeit (copies_unitary _ _ (siteRot_u k))) ?_ l); rw [swayC]; exact congr_arg (z • ·) (Subtype.ext (h ..)) -- order z?
lemma heatExp (l:Rays)(V:Grid c)(hH:Healthy p.threshold B V) (h:Woven o B p t f a) (hZ: ‖zz‖≤1)(hx:2^p.order*a≤1/4)(hp:1≤t): exp (plyM f zz l V) =1+ zz^Many.tier l • braid f 1 l V:=by
    exact (soothe _ ((le_trans ((braidLaw zz hp h hx hZ l).2 V hH) (holdsU h hx l)).trans_lt (by norm_num))).trans (congr_arg _ (congr_fun (braid_homo zz l (f:=f)) V)) -- infer
end YM.QCD.Stew.Phased
