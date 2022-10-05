<?php

use App\Http\Controllers\AuthController;
use App\Http\Controllers\DiscordController;
use App\Http\Controllers\ProjectController;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Route;

/*
|--------------------------------------------------------------------------
| API Routes
|--------------------------------------------------------------------------
|
| Here is where you can register API routes for your application. These
| routes are loaded by the RouteServiceProvider within a group which
| is assigned the "api" middleware group. Enjoy building your API!
|
*/

Route::post('login', [AuthController::class, 'login']);
Route::post('wallet-connect', [AuthController::class, 'walletConnect']);
Route::post('user', [AuthController::class, 'user']);
Route::put('profile', [AuthController::class, 'profile']);

Route::post('notification', [ProjectController::class, 'notification']);
Route::resource('projects', ProjectController::class);

Route::get('discord-connect', [DiscordController::class, 'discordConnect']);
Route::get('discord-callback', [DiscordController::class, 'discordCallback']);
Route::get('discord-info', [DiscordController::class, 'discordInfo']);
Route::get('discord-servers', [DiscordController::class, 'discordServers']);
Route::get('guild-preview/{id}', [DiscordController::class, 'guildPreview']);
Route::get('discord-channels/{id}', [DiscordController::class, 'discordChannels']);
Route::get('discord-messages/{id}', [DiscordController::class, 'discordMessages']);
Route::get('discord-disconnect', [DiscordController::class, 'discordDisconnect']);

Route::get('user', [AuthController::class, 'user']);
