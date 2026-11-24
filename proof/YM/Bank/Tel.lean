import YM.Bank.Live
import YM.QCD.Flume.Ear
/-! # Cumulative exact engineering comparison through stationary letter-count j, kernels on radial stencils. No operator norms or truncations in this telescope. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank
open Function Precision Matrix Lattice Wilson Laurent Bloch Exterior YM.Next.Free
open Work.F06 Finset Filter Metric RG
open AnalyticBridge.LocalGaussianLaws.Current
open QCD.Flume (twins tunes)
open scoped Matrix BigOperators Topology ComplexConjugate InnerProductSpace Matrix.Norms.L2Operator

variable {c f k m:Side}{i j t:ℕ}

def loom (r:Ratio c f)(s:Ratio f k) : Ratio c k := ⟨r.count*s.count,by rw [s.exact_size,r.exact_size,PNat.mul_coe,mul_assoc]⟩
def idle (c:Side) : Ratio c c:= ⟨1,by rw [show PNat.val 1=1 from rfl,mul_one]⟩
lemma twins_loom (r:Ratio c f)(s:Ratio f k)(ho:Odd r.count.val)(hu:Odd s.count.val)(p:Site c)(l:Site r.count)(q:Site s.count) : twins (loom r s) p (radices ho hu (l,q))=twins s (twins r p l) q := by
   apply lift_inj; have ht:Odd ((loom r s).count.val):= ho.mul hu
   rw [QCD.Flume.twin_lift _ ht,QCD.Flume.twin_lift _ hu,QCD.Flume.twin_lift _ ho,show radices ho hu (l,q)=jointAlias _ _ l q from rfl]; dsimp only [loom]; rw [joint_lift ho hu,r.exact_size,smul_add, ← mul_smul,add_assoc]
lemma twins_r (p:Site c)(l:Site (idle c).count) : twins (idle c) p l=p := by
    letI :Subsingleton (Site 1):=inferInstanceAs (Subsingleton (Axis → ZMod 1)) -- no
    change Site 1 at l; have he:l=(0:Site 1):=Subsingleton.elim ..; rw [twins,he]; dsimp only [idle]; simp

def sprout (j:ℕ)(r:Side)(p:Momentum):ℂ:=area r p ^ j
def spindle (j:ℕ)(r:Side)(p:Momentum)(i:Axis) := sprout j r p * rail r (p i)
lemma box_bind {K L:Side} (hk:Odd K.val) (hl:Odd L.val)(p:Momentum) (q: Site L): sprout j (K*L) (aliasAt p q)= sprout j K p * sprout j L (aliasAt p q) :=by
   unfold sprout; rw [←mul_pow]; congr 1
   have he A: area (K*L) A= area K (L.val • A)*area L A:=by unfold area; rw [← Finset.prod_mul_distrib]; apply prod_congr rfl; intro i _; rw [Pi.smul_apply,nsmul_eq_mul, plank_bind _ _ hk hl]
   rw [he,alias_scale,Train.area_period]
lemma spindle_merges {K L:Side}(hk:Odd K.val) (hl:Odd L.val)(p:Momentum)(q:Site L)(i:Axis): spindle j (K*L) (aliasAt p q) i=spindle j K p i * spindle j L (aliasAt p q) i:=by
   unfold spindle; rw [box_bind hk hl, ← rail_bind]; have he:=congr_fun (alias_scale p q) i; simp only [nsmul_eq_mul,Pi.mul_apply,Pi.add_apply,Pi.natCast_apply,Laurent.reciprocal] at he; rw [he,rail_repeat]; ring -- direction?
-- gauge mean kernels. Character amplitude on any tag
section Total

def warp (j:ℕ) {c f:Side}(r:Ratio c f)(p:Momentum):Matrix (TypeFace 1) (Co r.count (TypeFace 1)) ℂ:=
     upAlias fun l : Site r.count => (r.count.val:ℂ) • mask 1 (spindle j r.count (aliasAt p l))
def quota (j:ℕ){c f:Side}(r:Ratio c f)(Q: Matrix (Body 1 c) (Body 1 f) ℝ) := Runs (rotations c (TypeFace 1)) (readings r (TypeFace 1)) Q (solo c (warp j r))
lemma runs_entry (j:ℕ) (r:Ratio c f)(Q: Matrix (Body 1 c) (Body 1 f) ℝ): quota j r Q ↔ ∀ (i:Body 1 c)(p:Site c)(l:Site r.count)(a:TypeFace 1),
      (approached Q*readings r (TypeFace 1)) i (p,l,a)=if i.2=a then cell p i.1 *((r.count.val:ℂ)*spindle j r.count (aliasAt (mon p) l) (axisEquiv.symm a)) else 0 :=by
   have hx (x:Site c) (p:Site c)(l:Site r.count)(a b:TypeFace 1) : (rotations c (TypeFace 1)* solo c (warp j r)) (x,b) (p,l,a)= if b=a then (cell p x)*((r.count.val:ℂ)*spindle j r.count (aliasAt (mon p) l) (axisEquiv.symm a)) else (0:ℂ):=by
     rw [solo,rot_fiber]; change cell p x*((r.count.val:ℂ) • mask 1 (spindle _ _ _)) b a=_; rw [Matrix.smul_apply, mask_value]; simp only [smul_eq_mul,mul_ite,mul_zero]; split
     next h=> subst a; rfl
     rfl
   refine ⟨fun h i p l a=>?_,fun H=>?_⟩
   · obtain ⟨x,b⟩:=i; unfold quota Runs at h; rw [h,hx]
   unfold quota Runs; ext ⟨x,b⟩ ⟨p,l,a⟩; rw [H,hx]
lemma quota_add {r:Ratio c f}{s:Ratio f k}{Q: Matrix (Body 1 c) (Body 1 f) ℝ}{X:Matrix (Body 1 f) (Body 1 k) ℝ}(ho:Odd r.count.val)(he:Odd s.count.val)(h:quota j r Q)(g:quota j s X) : quota j (loom r s) (Q*X):=by
   refine (runs_entry ..).mpr fun ⟨x,b⟩ p u a=>?_
   obtain ⟨⟨l,q⟩,rfl⟩:=(radices ho he).surjective u; dsimp only
   let i:= (tunes r ho (p,l)); change Site _ at i -- ?
   let L:= loom r s; let z:= radices ho he (l,q); let I:= TypeFace 1
   have hx w v : (readings L (TypeFace 1)) w (p,z,v)=readings s (TypeFace 1) w (twins r p l,q,v):=by
       change readings (loom r s) I (w.1,w.2) _=readings s I (w.1,w.2) _
       rw [twin_leaf (loom r s) (Odd.mul ho he),twin_leaf s he]; rw [show twins (loom r s) p z=_ from twins_loom r s ho he p l q]
   let w:=twins r p l; let R:=(readings r (TypeFace 1)); let t:= spindle j s.count (aliasAt (mon w) q) (axisEquiv.symm a); let N:=(↑s.count.val:ℂ)*t
   have hz y : (approached X*readings L (TypeFace 1)) y (p,z,a) = R y (p,l,a) * N:= by
       have hk := (runs_entry _ _ _).mp g y w q a
       have hy : (approached X*readings L (TypeFace 1)) y (p,z,a)=(approached X*readings s (TypeFace 1)) y (w,q,a) :=by rw [Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro b _; rw [hx]
       rw [hy,hk]; rcases y with ⟨y,f⟩; rw [show R (y,f) (p,l,a)=rotations _ (TypeFace 1) (y,f) (w,a) from twin_leaf _ ho ..]; unfold rotations; simp only [Matrix.of_apply,ite_mul,zero_mul]; rfl
   rw [prom_mul];
   calc
     _ = (approached Q * R) (x,b) (p,l,a) * N := by rw [Matrix.mul_assoc,Matrix.mul_apply, Matrix.mul_apply, sum_mul]; refine sum_congr rfl fun y _ => ?_; rw [show (approached X*readings (loom r s) (TypeFace 1)) y _=_ from hz y]; ring
     _ = _ := by
       rw [show (approached Q * R) (x,b) (p,l,a)=_ from (runs_entry _ _ _).mp h (x,b) p l a]; dsimp only
       split
       next hg=> unfold N t w; rw [twin_mon r ho]; unfold loom; dsimp only; rw [← alias_refine,spindle_merges ho he,mul_side_complex]; ring
       simp
lemma quota_nil (c:Side)(j:ℕ):quota j (idle c) 1:=by
     apply (runs_entry ..).mpr; rintro ⟨x,v⟩ p l a
     have ht: approached (1:Matrix (Body 1 c) (Body 1 c) ℝ)=1:=by ext i j; by_cases h:i=j <;> simp [h,approached,Matrix.one_apply]
     rw [ht,Matrix.one_mul, twin_leaf _ odd_one, twins_r]; unfold rotations; simp only [Matrix.of_apply]; split <;> simp_all [idle, spindle,sprout]
structure TowerW (j:ℕ)(r: Ratio c f) (A B : Bed)(J:Matrix (Body 2 f) (Body 2 c) ℝ)(R:Matrix (Body 1 f) (Body 1 c) ℝ)(Q: Matrix (Body 1 c) (Body 1 f) ℝ):Prop where
    odd: Odd r.count.val
    binds : J*d 1 c= d 1 f*R
    station : Precision.K (A.metric.acts f)*R=Q.transpose*Precision.K (B.metric.acts c)
    smooth : quota j r Q
variable {F B H:Bed}
lemma TowerW.merges {r:Ratio c f}{s:Ratio f k}{J J' R R' Q Q'} (h:TowerW j r B F J R Q) (g:TowerW j s H B J' R' Q') : TowerW j (loom r s) H F (J'*J) (R'*R) (Q*Q') where
    odd:=h.odd.mul g.odd
    binds := by rw [Matrix.mul_assoc,h.binds,← Matrix.mul_assoc J',g.binds,Matrix.mul_assoc]
    station :=by rw [← Matrix.mul_assoc, g.station, Matrix.mul_assoc, h.station, transpose_mul, Matrix.mul_assoc]
    smooth:= quota_add h.odd g.odd h.smooth g.smooth
lemma TowerW.single (S:StepData c f) (T:Towers S.patch.L) {p:Clip}{a b:ℝ}(h0:Floor H p f a b) (h:Towers.Diagonal S H B T) : TowerW S.patch.J S.ratio H B (psi S H B T) (installed S.ratio T.A0) (mean S) where
   odd:= S.patch.odd_side
   smooth:= patch_service S
   station:=h.trial.primal
   binds:= by
     unfold psi; rw [Matrix.mul_assoc, Matrix.mul_assoc (H.dual_diag.acts f),← Matrix.mul_assoc _ (B.diagonal.acts c), h.stays]; simp only [← Matrix.mul_assoc,mul_eq_one_comm.mp h0.diagonalInv,Matrix.one_mul]
lemma TowerW.empty (j:ℕ) {F:Bed}: TowerW j (idle c) F F 1 1 1:= ⟨odd_one,by rw [Matrix.mul_one,Matrix.one_mul],by rw [transpose_one,mul_one,one_mul],quota_nil c j⟩

end Total
end YM.Bank
#print axioms YM.Bank.TowerW.merges
#print axioms YM.Bank.TowerW.single
