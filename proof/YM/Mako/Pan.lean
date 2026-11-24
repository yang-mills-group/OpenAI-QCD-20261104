import YM.Mako.Jail
import YM.Mako.Dutch
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{W:Axis×Axis→ K.W} {A: Axle K (fun a b=>W (a,b))}{I:ℕ→ℕ} (J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(hd:8 ≤ d)
variable (R: Roof P.sym)
open Org
noncomputable abbrev camp(Q:Ortho.Skew):Module.End ℂ (K.level d):= tapeJ K W A hd Q
include H J JQ
lemma cash (p q:Ortho.Skew) : tapeJ K W A hd (p+q) = tapeJ K W A hd p+tapeJ K W A hd q:=by
     ext1 x; apply Subtype.ext; change A.jet (p+q) x.val= _; rw[A.addP H JQ.h]; rfl
lemma gain (r:ℝ)(p:Ortho.Skew): tapeJ K W A hd (r • p)=(r:ℂ) • tapeJ K W A hd p:=by
     ext1 x; apply Subtype.ext; change A.jet (r • p) x.val= _; rw [A.scaleP H]; rfl
noncomputable def yarn : Ortho.Skew →+ Module.End ℂ (K.level d):= {
     toFun:=tapeJ K W A hd,map_add':=cash J H JQ hd
     map_zero':=by rw [← zero_smul ℝ (0:Ortho.Skew),gain J H JQ hd]; simp }
include B
lemma whip(a b:Axis):Clear (tapeJ K W A hd (Ortho.plane a b)):=by
     obtain ⟨x,ha,hb,-⟩:= outside a b b; exact band _ _ (pinnacle H JQ W J.n A B hd a b x ha hb 1 zero_lt_one)
set_option quotPrecheck false
omit H J JQ B
lemma reduces {Z Y:Type*}[AddCommGroup Y][Module ℂ Y][FiniteDimensional ℂ Y]
       [NormedAddCommGroup Z][NormedSpace ℂ Z][FiniteDimensional ℂ Z](F:ℕ→ Z≃ₗ[ℂ]Y)(P Q M:Module.End ℂ Y)(p q:Module.End ℂ Z)(S:Tide Y)(hs:S.Leans (clip P Q-M))
       (hP:∀ v:Z,Tendsto (fun i:ℕ=>(F i).symm (P (F i v))) atTop (𝓝 (p v)))(hQ:∀ v:Z,Tendsto (fun i:ℕ=>(F i).symm (Q (F i v))) atTop (𝓝 (q v)))(hM:∀ v:Z,Tendsto (fun i:ℕ=>(F i).symm (M (F i v))) atTop (𝓝 (clip p q v))): clip P Q=M:=by
       apply sub_eq_zero.mp; by_contra h; let T:=clip P Q-M; let L(p:Module.End ℂ Y)(t:ℕ):Module.End ℂ Z:= (F t).symm.toLinearMap ∘ₗ p ∘ₗ (F t).toLinearMap
       have ht(v:Z): Tendsto (fun t=> L T t v) atTop (𝓝 (0:Z)):=by
             have he:= ((follows_L (L P) p hP _ _ (hQ v)).sub (follows_L (L Q) q hQ _ _ (hP v))).sub (hM v); change Tendsto _ atTop (𝓝 (clip p q v-clip p q v)) at he; rw[sub_self] at he; apply he.congr'; refine Eventually.of_forall fun i=>?_ ; change (L P i ( (F i).symm (Q _))- L Q i ((F i).symm (P _)))-(F i).symm (M _)= (F i).symm (T ((F i) v)); simp [L,T,clip]
       have hx:= track (L T) 0 ht; simp_rw [show ∀ i,LinearMap.trace ℂ Z ((L T i)^2)=LinearMap.trace ℂ Y (T^2) from fun i=> chord (F i) T] at hx; rw[zero_pow (by decide),map_zero] at hx
       have he : LinearMap.trace ℂ Y (T^2)=0:= tendsto_nhds_unique tendsto_const_nhds hx
       have hv:= Tide.billQ S T hs h; rw[he,Complex.zero_re,neg_zero] at hv; exact lt_irrefl _ hv
lemma helmet {Z:Type*}[AddCommGroup Z][Module ℂ Z](S:Tide Z)(F:Ortho.Skew→+ Module.End ℂ Z)(i:Axis)(hv:∀ a b:Axis,a≠i→b≠i→ S.Leans (F (Ortho.plane a b)))(a b m n:Axis)(ha:a≠i)(hb:b≠i)(hm:m≠i)(hn:n≠i): S.Leans (F (bracket (Ortho.plane a b) (Ortho.plane m n))):=by rw[Work.A09.bracket_planes,map_sub,map_add,map_sub]; refine lsub _ _ _ (lplus _ _ _ (lsub _ _ _ ?_ ?_) ?_) ?_ <;> split <;> first|(exact hv _ _ (by assumption) (by assumption))|(rw[F.map_zero]; exact lzero _)
include H J JQ B R
lemma oils : Clubs (yarn J H JQ hd):=by
     intro a b m n i ha hb hm hn
     let p:=Ortho.plane a b; let q:=Ortho.plane m n; let F:=yarn J H JQ hd
     change clip (F p) (F q)= _; change clip (F p) (F q)= F (bracket p q)
     let G:= clip (F p) (F q)- F (bracket p q); let S:= entryQ H JQ i 1 zero_lt_one d
     have hv(a b:Axis)(ha:a≠i)(hb:b≠i): S.Leans (F (Ortho.plane a b)):= pinnacle H JQ W J.n A B hd a b i ha hb 1 zero_lt_one
     have hm': S.Leans (F (bracket p q)):= helmet S F i hv _ _ _ _ ha hb hm hn
     have hS : S.Leans G:= lsub _ _ _ (lclip _ _ _ (hv _ _ ha hb) (hv _ _ hm hn)) hm'
     apply reduces (fun i=>X.frame (I i) d) (F p) (F q) (F (bracket p q)) (rain p d) (rain q d) _ hS (goes J hd p) (goes J hd q)
     unfold clip; rw[rue J H JQ.h hd p q R]; exact goes J hd (bracket p q)
lemma bridge (p q:Ortho.Skew): clip (tapeJ K W A hd p) (tapeJ K W A hd q)= tapeJ K W A hd (bracket p q):=
     palms (yarn J H JQ hd) (oils J H JQ B hd R) (whip J H JQ B hd) (gain J H JQ hd) p q
-- on physical jet W all (directed union)
omit hd
lemma stake (p q:Ortho.Skew): clip (A.jet p) (A.jet q)= A.jet (bracket p q):=by
     ext1 w; obtain ⟨i,h⟩:= JQ.h.absorbs w; let d:=max i 8; have ht:w∈ K.level d:= JQ.h.slope (le_max_left ..) h; let x:K.level d:= ⟨w,ht⟩; exact congr_arg Subtype.val (DFunLike.congr_fun (bridge J H JQ B (le_max_right i 8) R p q) x)
end YM.Mako
#print axioms YM.Mako.oils
#print axioms YM.Mako.stake
