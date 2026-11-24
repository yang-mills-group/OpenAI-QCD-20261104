import YM.Gust.Tuna
import YM.Gust.Yok
set_option maxHeartbeats 650000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Table Work.A01 Outer Tarn Tarn.Choir Tarn.Choir.Strip UV
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix Matrix.Norms.Frobenius
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){n m:ℕ}
variable (A:Axis×Axis→K.W)(hA:Tarn.ChargeQ.Persona T A) (J:Axle K (fun a b=>A (a,b)))(U:Vane J)
local notation "Jt"=>fun a b=>A (a,b)
include hK hf hA
open Finset
variable (g:Ortho.Skew)(a b k:Axis)
local notation "Tκ"=> Ch T k
variable (v w:K.W)(p q:Bool)(hv:v∈ Col T p)(hw:w∈Col T q)
include hv hw
lemma diamond(x:Points 2)(h:x∈conf _) : K.total _ x (![J.jet g (Ch T k v),Ch T k w]) = K.total _ x (![Ch T k (J.jet g v),Ch T k w]):=by
       obtain ⟨χ,hχ⟩:= Work.A01.exists_window x h; have hY(u W:K.W): about (Jt) χ (Outer.roll g) x (![u,W])= K.total _ x (![J.jet g u,W]):= (J.relation g _ 1 x χ h hχ (![W])).trans (heads ..)
       let c:=cSign p q
       have ht: J.jet g v∈Col T p:= by rw[hue, ← Axle.colors hK hf A hA,hue T v p |>.1 hv,map_smul]
       rw [star2 hK hf A hA p q _ _ ht hw k h, ← hY, ← hY]
       let τ(y:E4):= roll g (y-x 0); let F(a b:Axis):= termG (Jt) χ τ x (![v,w]) a b
       have he(a b : Axis)(y): termG (Jt) χ τ x (![Ch T k v,Ch T k w]) a b y= c * star (F a b y):=by
             by_cases hx: D (basis a) χ y=0; · simp[F,termG,hx]
             unfold F termG; rw [show K.total _ _ (Fin.cons (A (a,b)) (![Tκ v,Tκ w]))= _ from star3 hK hf A hA p q v w hv hw k h y a b (separated_of_D h hχ hx)]; unfold phot; rw [star_mul]; push_cast; simp[c]; ring
       unfold about fluxG; change -(∑ a:Axis,∑ b:Axis,∫ y, termG (Jt) χ τ x (![Ch T k v,Ch T k w]) a b y) = c * star (-(∑ a:Axis,∑ b:Axis,∫ y,F a b y)); simp_rw [he,integral_const_mul]; simp_rw [Complex.star_def, integral_conj]; simp only [map_neg,map_sum]; rw [mul_neg,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro i _; rw [Finset.mul_sum]
omit hv hw
include hv
lemma pearl : J.jet g (Ch T k v)=Ch T k (J.jet g v) :=by
       let X:= J.jet g (Ch T k v); let W:= Ch T k (J.jet g v); have he(w:K.W)(x:Points 2)(hx:x∈conf _): K.total _ x (![X,Tκ w])=K.total _ x (![W,Tκ w]):=by
             obtain ⟨u,hu,y,hy,H⟩:= by_color (T:=T) hK w; have ha(w:K.W)(x:Points 2)(u v:K.W): K.total _ x (![w,u+v])= K.total _ x (![w,u])+K.total _ x (![w,v]):=by
                  let L(t:K.W):= (K.total 2 x).toLinearMap (![w,(0:K.W)]) 1 t; have h(t): L t=K.total _ x (![w,t]):=by unfold L; refine congr_arg (K.total _ _) ?_; funext i; fin_cases i <;> simp
                  rw[←h,←h,←h]; exact map_add ..
             rw [H,map_add,ha,ha]; exact congr_arg₂ (· + ·) (diamond hK hf A hA J g k _ u _ _ hv hu x hx) (diamond hK hf A hA J g k _ y _ _ hv hy x hx)
       by_contra h; obtain ⟨w,hw⟩:= (T.adj k).surjective (X-W); have hW : w≠0:=by intro he; rw[he,map_zero] at hw; exact h (sub_eq_zero.mp hw.symm)
       obtain ⟨r,hR,hx⟩:= hf.realPair k w hW; obtain ⟨u,hu⟩:= (Tκ).surjective w; let z:= points (![0,r • basis k]); have hZ : z∈conf _:=by
            have hS:r • basis k≠0:=by intro h; have e:=congr_arg (fun x:E4=>x k) h; simp [basis] at e; linarith
            intro i j h; fin_cases i <;>fin_cases j<;> simp [z,Ne.symm hS,hS] at *
       rw[hw] at hx; apply hx.ne'; change K.total 2 z _= 0; have hh:headG (![w]) z (X-W)=0:=by rw [map_sub, heads,heads]; apply sub_eq_zero.mpr; rw [←hu]; exact he u z hZ
       rw [heads] at hh; exact hh
omit hv
lemma axle_Ch (w:K.W): J.jet g (Ch T k w)= Ch T k (J.jet g w):=by
       obtain ⟨x,hx,y,hy,h⟩:= by_color (T:=T) hK w; rw[h,map_add,map_add,map_add,map_add]; exact congr_arg₂ (· + ·) (pearl hK hf A hA J g k x _ hx) (pearl hK hf A hA J g k y _ hy)
omit hf hK hA
variable (ht:a≠k)(hz:b≠k)
include ht hz
lemma wavedP (x:E4): roll (Ortho.plane a b) (Ortho.move (Signed.reflect k) x)= Ortho.move (Signed.reflect k) (roll (Ortho.plane a b) x):=by
       ext1 j; rw [Signed.mirrored k j _,roll_plane]; simp_rw [Signed.mirrored,roll_plane]; by_cases h:j=a <;> by_cases hp:j=b <;> by_cases hX:j=k <;> simp_all
lemma kinder : Org.orients (Signed.mirror k) (Ortho.plane a b)= Ortho.plane a b :=by
       let G:= Ortho.plane a b; let s:= Signed.mirror k; let E:= Ortho.motion s.ortho
       have h(x:E4) : roll (Org.orients s G) x= roll G x:=by
              obtain ⟨y,rfl⟩:= E.surjective x
              have H: Ortho.move s.ortho 0=0:= map_zero E
              change M4.move _ (Ortho.move s.ortho y)=_; nth_rw 1 [← sub_zero (Ortho.move s.ortho y), ← H]; rw[Work.A01.move_rotation s G 0 y,sub_zero]; exact (wavedP a b k ht hz y).symm
       refine Subtype.ext (Matrix.ext fun i j=>?_); refine Eq.trans (M4.move_basis (Org.orients s G).val i j).symm (Eq.trans ?_ (M4.move_basis G.val i j)); exact congr_arg (fun p:E4=>p i) (h (basis j))
include hf hK hA
lemma eye_h (w:K.W): J.jet (Ortho.plane a b) (T.adj k w)= T.adj k (J.jet (Ortho.plane a b) w):=by
       rw [←steal T hK k w, ←steal T hK k (J.jet (Ortho.plane a b) w),← axle_Ch hK hf A hA J (Ortho.plane a b) k]
       have hh:=liven A hf J hA (Signed.mirror k) _ (couture k) (Ortho.plane a b) (Tκ w); rwa[kinder a b k ht hz] at hh
include U
lemma skewJ (x y:K.W)(t:ℝ)(hy:0<t) : let g:=Ortho.plane a b; let F:=points (![0,t • basis k]); K.total 2 F (![T.adj k (J.jet g x),y])= -K.total 2 F (![T.adj k x,J.jet g y]):=by
       intro g F; have hs:F∈conf _:=by
            have hS:t • basis k≠0:=by intro h; have e:=congr_arg (fun x:E4=>x k) h; simp [basis] at e; linarith
            intro i j h; fin_cases i <;>fin_cases j<;> simp [F,Ne.symm hS,hS] at *
       have hk: Ward.onLine k F:=by intro i; fin_cases i; exact ⟨0,(zero_smul ..).symm⟩; exact ⟨t,rfl⟩
       have hL:= Gust.line hK hf A hA J U (m:=1) F hs (![T.adj k x,y]) k g hk
       have he(i:Fin 2)(c:Axis): roll g (F i) c=0:=by rw [show g=Ortho.plane a b from rfl,roll_plane]; fin_cases i <;>simp [F,basis,hz,ht]
       let v:=( ![T.adj k x,y]); have hv(i:Fin 2): swirl K A J U g (F i) (v i)=J.jet g (v i):=by unfold swirl; change _ + (∑ c:Axis, (roll g (F i) c:ℂ) • _) = _; simp[he]
       unfold valor at hL; change ∑ i:Fin 2,K.total _ F (Function.update v i (swirl K A J U g (F i) (v i)))=0 at hL; simp_rw[hv] at hL; rw [Fin.sum_univ_succ,Fin.sum_univ_one] at hL; apply eq_neg_of_add_eq_zero_left; rw [←eye_h hK hf A hA J a b k ht hz]; convert hL using 2 <;> first | rfl | (apply congr_arg; funext i; fin_cases i <;> simp [g,v])
end YM.Massive.Gust
#print axioms YM.Massive.Gust.skewJ
