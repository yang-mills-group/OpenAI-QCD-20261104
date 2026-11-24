import YM.DawnS.Trays
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
local notation "I₀"=>Complex.I
local notation "P"=> RingS
local notation "Ω"=>muS
variable {d:ℕ}
abbrev Peak (d:ℕ):=chit d × Pinor
abbrev UAtom(k: Flavor 6)(z:Hue)(v:Bool)(x:Peak d):= lantern ((k,z,v,x):Vault d)
lemma ray_L {r:ℝ}(hr:0<r)(i j:Hue)(k t: Flavor 6)(v w:Bool)(a b:Peak d) (h: (i,k,v)≠(j,t,w)):sigL r (UAtom k i v a) (UAtom t j w b)=0:=by
     rcases a with ⟨x,a⟩; rcases b with ⟨y,b⟩; cases v <;> cases w
     · exact (inColor x y a b i j k t r hr|>.trans (if_neg fun e=>h (by rw [e.1,e.2]))) -- args hr
     · exact across x y a b i j k t r hr
     · exact toward x y a b i j k t r hr
     exact (barColor x y a b i j k t r hr|>.trans (if_neg fun e=>h (by rw [e.1,e.2])))
noncomputable def shot(v:Bool)(p:Peak d)(J:Pinor)(r:ℝ)(x:PR):ℂ:= lampS v x.2 J p.2 * gleam v p.1 r x
lemma continuousLamp(v:Bool)(a b:Pinor):Continuous fun z:P=>lampS v z a b:=by
     cases v
     · change Continuous fun z:P=>(shine 1 z *gamma K) b a; simp_rw[Matrix.mul_apply]; exact continuous_finsetSum _ (fun i _=> (shines 1 b i).mul continuous_const)
     change Continuous (fun z:P=> -((gamma K*shine (-1) z) a b)); simp_rw [Matrix.mul_apply]; exact (continuous_finsetSum _ (fun i _=>continuous_const.mul (shines (-1) i b))).neg
lemma continuousShot (v:Bool)(p:Peak d)(J:Pinor)(r:ℝ):Continuous (shot v p J r):=((continuousLamp v J p.2).comp continuous_snd).mul (gleams ..)
-- Bilinear cost law. t weights. arrangement.
variable (p q:Peak d) (i:Hue)(k:Flavor 6)(r:ℝ)(hr:0<r)(c:Bool)(y:Pinor)
set_option quotPrecheck false
local notation "Φp"=> fun z=>phaseG p.1 c z * lampS c z y p.2
local notation "Φq"=> fun z=>phaseG q.1 c z * lampS c z y q.2
noncomputable abbrev sparksT (p q:Peak d)(c:Bool)(r:ℝ)(y:Pinor)(x:PR):ℂ:=priceK r x.1 * (star (shot c p y r x)*shot c q y r x)
-- existence integrable & value
local notation "F"=> sparksT p q c r y
local notation "n"=> (listP p.1).length+(listP q.1).length
lemma flows: Integrable (F) wa ∧ (∫ z:PR,F z ∂wa)=(rayG r ((listP p.1).length+(listP q.1).length+1):ℂ) * (∫ z:P,star ((Φp) z)*(Φq) z ∂Ω):=by
     let L:=Φp; let Q:=Φq
     rw [show F=(fun x:PR=>((↑(priceK r x.1):ℂ)* ((↑(x.1/r):ℂ)^((listP p.1).length+(listP q.1).length)))*(star (L x.2)*Q x.2)) from ?h]; swap
     · ext1 x; unfold L Q sparksT shot gleam; rw [pow_add]; simp only [star_mul,star_pow, Complex.star_def, Complex.conj_ofReal]; ring
     exact tallyCup r _ _ (((fluidG p.1 c).mul (continuousLamp c _ _)).star.mul ((fluidG q.1 c).mul (continuousLamp c _ _)))
include hr
lemma ricket: (2:ℂ)*sigL r (UAtom k i c p) (UAtom k i c q) = ∑ y:Pinor, ∫ z:PR,sparksT p q c r y z ∂wa:=by
     let T:=(rayG r (n+1):ℂ)
     have h: sigL r (UAtom k i c p) (UAtom k i c q)= T * (∫ z:P,star (phaseG p.1 c z) *phaseG q.1 c z *lampS c z p.2 q.2 ∂Ω):=by
           cases p; cases q; cases c; exact ((inColor _ _ _ _ _ _ _ _ r hr).trans (if_pos ⟨rfl,rfl⟩)); exact ((barColor _ _ _ _ _ _ _ _ r hr).trans (if_pos ⟨rfl,rfl⟩))
     simp_rw [fun y=> (flows p q r c y).2]; rw [h,mul_left_comm,← integral_const_mul]; rw [← Finset.mul_sum, ← integral_finsetSum]
     swap; · intro k _; exact ((((fluidG p.1 c).mul (continuousLamp c k p.2)).star.mul ((fluidG q.1 c).mul (continuousLamp c k q.2))):Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
     refine congr_arg (T* ·) (integral_congr_ae (Eventually.of_forall fun z=>?_))
     have he:= congr_fun (congr_fun (powered z c) p.2) q.2; dsimp only at he ⊢; rw [Matrix.smul_apply,smul_eq_mul] at he; rw [show (2:ℂ)*(_*_)=star (phaseG p.1 c z)*phaseG q.1 c z*(2*lampS c z p.2 q.2) from ?_]
     · rw [←he, Matrix.mul_apply, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; simp only [phaseG,star_mul]; ring
     ring
end YM.DawnS
