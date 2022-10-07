<?php

namespace App\Http\Controllers;

use App\Notifications\EmailVerification;
use Carbon\Carbon;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Hash;
use App\Models\User;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use Twilio\Rest\Client;

class AuthController extends Controller
{
    public function __construct()
    {
        $this->middleware('auth:api', ['except' => ['login','register', 'walletConnect', 'verifyEmail']]);
    }

    public function login(Request $request)
    {
        $request->validate([
            'email' => 'required|string|email',
            'password' => 'required|string',
        ]);
        $credentials = $request->only('email', 'password');

        $token = Auth::attempt($credentials);
        if (!$token) {
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid email or password',
            ]);
        }

        $user = Auth::user();
        return response()->json([
            'status' => 'success',
            'user' => $user,
            'token' => $token,
        ]);

    }

    public function register(Request $request){

        $validator = Validator::make($request->all(), [
            'name' => 'required|string|max:255',
            'email' => 'required|string|email|max:255|unique:users',
            'password' => 'required|string|min:6',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors(),
            ]);
        }

        $user = new User();
        $user->name = $request->get('name');
        $user->email = $request->get('email');
        $user->wallet_address = $request->get('wallet_address');
        $user->password = Hash::make($request->get('password'));
        $user->is_admin = $request->get('is_admin');
        $user->save();

        Auth::login($user);
        return response()->json([
            'status' => 'success',
            'message' => 'User created successfully',
            'user' => $user,
        ]);
    }

    public function walletConnect(Request $request){

        $validator = Validator::make($request->all(), [
            'wallet_address' => 'required|string|max:255',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => 'Wallet address not found',
            ]);
        }

        $user = User::updateOrCreate([
            'wallet_address' => $request->get('wallet_address'),
        ]);

        $token = Auth::login($user);
        return response()->json([
            'status' => 'success',
            'message' => 'Wallet connected successfully',
            'user' => $user,
            'token' => $token
        ]);
    }

    public function logout()
    {
        Auth::logout();
        return response()->json([
            'status' => 'success',
            'message' => 'Successfully logged out',
        ]);
    }

    public function refresh()
    {
        return response()->json([
            'status' => 'success',
            'user' => Auth::user(),
            'token' => Auth::refresh(),
        ]);
    }

    public function profile(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'name' => 'required|string|max:255',
            'email' => 'required|string|email|max:255|unique:users,id,'.Auth::user()->id,
            'country_code' => 'required|string|max:255',
            'phone_number' => 'required|string|max:255',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors(),
            ]);
        }

        $user = Auth::user();

        if ($user->email != $request->get('email')) {
            $user->email_verified_at = null;
        }

        if ($user->country_code != $request->get('country_code') || $user->phone_number != $request->get('phone_number')) {
            $user->phone_verified_at = null;
        }

        $user->name = $request->get('name');
        $user->email = $request->get('email');
        $user->country_code = $request->get('country_code');
        $user->phone_number = $request->get('phone_number');
        $user->save();

        return response()->json([
            'status' => 'success',
            'message' => 'Profile updated successfully',
            'user' => $user,
        ]);
    }

    public function verificationCode()
    {
        try{
            $user = Auth::user();
            $phone_number = $user->country_code . $user->phone_number;

            $sid = env('TWILIO_SID');
            $token = env('TWILIO_TOKEN');
            $verification_service = env('TWILIO_VERIFICATION_SERVICE');
            $twilio = new Client($sid, $token);

            $twilio->verify->v2->services($verification_service)
                ->verifications
                ->create($phone_number, "whatsapp", ["locale" => "en"]);

            return response()->json([
                'status' => 'success',
                'message' => 'Verification code sent successfully',
            ]);

        } catch(\Exception $ex){
            return response()->json([
                'status' => 'error',
                'message' => 'Please enter correct phone number and country code.',
            ]);
        }

    }

    public function verifyPhoneNumber(Request $request)
    {
        $validator = Validator::make ( $request->all () , [
            'verification_code'        => 'required' ,
        ] );

        if ( $validator->fails () ) {
            return response ()->json ( [
                'status'  => 'error' ,
                'message' => 'Please enter verification code.' ,
            ] );
        }

        try {

            $user = Auth::user ();
            $phone_number = $user->country_code . $user->phone_number;
            $code = Str::of($request->get('verification_code'))->trim();

            $sid = env('TWILIO_SID');
            $token = env('TWILIO_TOKEN');
            $twilio = new Client($sid, $token);
            $verification_service = env('TWILIO_VERIFICATION_SERVICE');

            $verification_check = $twilio->verify->v2->services ($verification_service)
                ->verificationChecks
                ->create ( [
                    "to" => $phone_number,
                    "code" => $code
                ]);

            if ( $verification_check->status == 'approved' ) {
                $user->phone_verified_at = Carbon::now();
                $user->save ();
                return response ()->json ( [
                    'status'  => 'success' ,
                    'message' => 'Phone number verified successfully.' ,
                    'user' => $user
                ] );
            }
            else {
                return response ()->json ( [
                    'status'  => 'error' ,
                    'message' => 'Code doesn\'t match.' ,
                ] );
            }
        }catch (\Exception $ex){
            return redirect ()->back ()->withInput ()->with ( 'errors' , 'Something went wrong.' );

        }
    }

    public function sendVerificationEmail()
    {
        try {
            $user = Auth::user();

            $id = $user->id;
            $hash = sha1($user->email);

            $user->notify(new EmailVerification($id, $hash));

            return response()->json([
                'status' => 'success',
                'message' => 'We just sent you a verification email on '.$user->email.'. Please check your inbox (or spam) to verify your email address.',
            ]);
        } catch (\Exception $exception) {
            return response()->json([
                'status' => 'error',
                'message' => 'Could not send verification email, please try again.',
            ]);
        }
    }

    public function verifyEmail ( $id , $hash ) {
        try {
            $user = User::find($id);

            if ($user && sha1($user->email) == $hash) {
                $user->email_verified_at = Carbon::now();
                $user->save();

                return redirect('/#/profile');

            } else {
                return response()->json([
                    'status' => 'error',
                    'message' => 'Invalid verification link.',
                ]);
            }
        } catch (\Exception $exception) {
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid verification link.',
            ]);
        }
    }

    public function userInfo()
    {
        $user = Auth::user();
        return response()->json([
            'status' => 'success',
            'user' => $user,
        ]);
    }

}
