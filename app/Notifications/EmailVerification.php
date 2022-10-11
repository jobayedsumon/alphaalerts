<?php

namespace App\Notifications;

use App\Models\User;
use Illuminate\Bus\Queueable;
use Illuminate\Contracts\Queue\ShouldQueue;
use Illuminate\Notifications\Messages\MailMessage;
use Illuminate\Notifications\Notification;
use Illuminate\Support\Facades\Lang;

class EmailVerification extends Notification implements ShouldQueue
{
    use Queueable;

    public $id;
    public $hash;

    /**
     * Create a new notification instance.
     *
     * @return void
     */
    public function __construct($id, $hash)
    {
        $this->id = $id;
        $this->hash = $hash;
    }

    /**
     * Get the notification's delivery channels.
     *
     * @param  mixed  $notifiable
     * @return array
     */
    public function via($notifiable)
    {
        return ['mail'];
    }

    /**
     * Get the mail representation of the notification.
     *
     * @param  mixed  $notifiable
     * @return \Illuminate\Notifications\Messages\MailMessage
     */
    public function toMail($notifiable)
    {
        return (new MailMessage)
            ->subject('Alpha Alerts - Verify your email address')
            ->line(Lang::get('Please click the button below to verify your email address.'))
            ->action(Lang::get('Verify Email Address'),  env('APP_URL').'/api/verify-email/' . $notifiable->id . '/' . $this->hash)
            ->line(Lang::get('If you did not create an account, no further action is required.'));
    }

    /**
     * Get the array representation of the notification.
     *
     * @param  mixed  $notifiable
     * @return array
     */
    public function toArray($notifiable)
    {
        return [
            //
        ];
    }
}
